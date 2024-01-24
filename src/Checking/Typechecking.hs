module Checking.Typechecking (checkTerm, unifyTerms, unifyToLeft, inferTerm, normaliseTermFully, checkProgram) where

import Checking.Context
  ( Tc,
    TcError (..),
    TcState (..),
    addItem,
    addTyping,
    enterCtx,
    enterCtxMod,
    enterGlobalCtxMod,
    enterPat,
    freshHole,
    freshHoleVar,
    freshVar,
    inCtx,
    inGlobalCtx,
    inState,
    isPatBind,
    lookupItemOrCtor,
    lookupType,
    modifyCtx,
    modifyGlobalCtx,
  )
import Checking.Vars (Sub (..), Subst (sub), alphaRename, noSub, subVar)
import Control.Monad (replicateM)
import Control.Monad.Except (catchError, throwError)
import Data.Bifunctor (second)
import Lang
  ( Clause (..),
    CtorItem (..),
    DataItem (..),
    DeclItem (..),
    Item (..),
    Pat,
    Program (..),
    Term (..),
    TermValue (..),
    Type,
    TypeValue,
    Var,
    genTerm,
    listToApp,
    listToPiType,
    locatedAt,
    mapTermM,
    piTypeToList,
    prependPatToClause,
  )

-- | Check the program
checkProgram :: Program -> Tc Program
checkProgram (Program decls) = Program <$> mapM checkItem decls

-- | Check some item in the program.
checkItem :: Item -> Tc Item
checkItem (Decl decl) = Decl <$> checkDeclItem decl
checkItem (Data dat) = Data <$> checkDataItem dat

-- | Check a data item.
checkDataItem :: DataItem -> Tc DataItem
checkDataItem (DataItem name ty ctors) = do
  -- Check the signature of the data type.
  s <- checkTerm ty (locatedAt ty TyT)
  let (tys, ret) = piTypeToList (sub s ty)
  ret' <- unifyToLeft ret (locatedAt ret TyT)
  let ty' = listToPiType (tys, ret')

  -- Then, add the declaration to the context.
  ctors' <- enterGlobalCtxMod (addItem (Data (DataItem name ty' ctors))) $ do
    -- Then, check each constructor.
    mapM (checkCtorItem ty') ctors

  -- Now add the final data type to the context.
  let dTy = DataItem name ty' ctors'
  modifyGlobalCtx (addItem (Data dTy))
  return dTy

checkCtorItem :: Type -> CtorItem -> Tc CtorItem
checkCtorItem dTy (CtorItem name ty dTyName) = do
  -- The amount of arguments of the data type
  let dTyArgCount = length . fst $ piTypeToList dTy

  -- Check the signature of the constructor.
  s <- checkTerm ty (genTerm TyT)
  let ty' = sub s ty
  let (tys, ret) = piTypeToList ty'

  -- \| Add all the arguments to the context
  ret' <- enterCtxMod (\c -> foldr (\(v, t) c' -> addTyping v t False c') c tys) $ do
    -- \| Check that the return type is the data type.
    dummyArgs <- replicateM dTyArgCount freshHole
    let dummyRet = listToApp (genTerm (Global dTyName) : dummyArgs)
    s' <- unifyTerms ret dummyRet
    return $ sub s' ret

  let ty'' = listToPiType (tys, ret')
  return (CtorItem name ty'' dTyName)

-- | Check a declaration.
-- This is self-contained, so it does not produce a substitution.
checkDeclItem :: DeclItem -> Tc DeclItem
checkDeclItem decl = do
  -- First, check the type of the declaration.
  let ty = declTy decl
  s1 <- checkTerm ty (genTerm TyT)

  -- Substitute the type.
  let ty' = sub s1 ty
  let tys = piTypeToList ty'
  let decl' = decl {declTy = ty'}

  -- The, add the declaration to the context.
  clauses <- enterGlobalCtxMod (addItem (Decl decl')) $ do
    -- Then, check each clause.
    mapM (enterCtx . checkClause tys) (declClauses decl')

  -- Substitute back into the type
  let decl'' = decl' {declClauses = clauses}
  modifyGlobalCtx (addItem (Decl decl''))
  return decl''

-- | Check a clause against a list of types which are its signature.
checkClause :: ([(Var, Type)], Type) -> Clause -> Tc Clause
checkClause ([], t) (Clause [] r) = do
  s <- checkTerm r t
  return (Clause [] (sub s r))
checkClause ((v, a) : as, t) (Clause (p : ps) r) = do
  pt <- patToTerm p
  s <- enterPat $ checkTerm pt a
  let instantiatedPat = sub s pt
  let s' = s <> Sub [(v, instantiatedPat)]
  c <- checkClause (map (second (sub s')) as, sub s' t) (Clause ps r)
  return $ prependPatToClause p c
checkClause ([], _) cl@(Clause (p : _) _) = throwError $ TooManyPatterns cl p
checkClause ((_, t) : _, _) cl@(Clause [] _) = throwError $ TooFewPatterns cl t
checkClause _ (ImpossibleClause _) = error "Impossible clauses not yet supported"

-- | Check the type of a term.
--
-- The location of the type is inherited from the term.
checkTermExpected :: Term -> TypeValue -> Tc Sub
checkTermExpected v t = checkTerm v (locatedAt v t)

-- | Check the type of a term. (The type itself should already be checked.)
-- This might produce a substitution.
checkTerm :: Term -> Type -> Tc Sub
checkTerm ((Term (Lam v t) _)) ((Term (PiT var' ty1 ty2) _)) = do
  enterCtxMod (addTyping v ty1 False) $ checkTerm t (alphaRename var' v ty2)
checkTerm t@((Term (Lam v t1) d1)) typ = do
  varTy <- freshHole
  bodyTy <- enterCtxMod (addTyping v varTy False) $ inferTerm t1
  let inferredTy = locatedAt d1 (PiT v varTy bodyTy)
  s1 <- unifyTerms typ inferredTy
  s2 <- checkTerm (sub s1 t) (sub s1 inferredTy)
  return $ s1 <> s2
checkTerm (Term (Pair t1 t2) _) (Term (SigmaT v ty1 ty2) _) = do
  s1 <- checkTerm t1 ty1
  s2 <- checkTerm (sub s1 t2) (subVar v (sub s1 t1) (sub s1 ty2))
  return $ s1 <> s2
checkTerm t@(Term (Pair _ _) d1) typ = do
  fstTy <- freshHole
  sndTy <- freshHole
  v <- freshVar
  let inferredTy = locatedAt d1 (SigmaT v fstTy sndTy)
  s1 <- checkTerm t inferredTy
  s2 <- unifyTerms typ (sub s1 inferredTy)
  return $ s1 <> s2
checkTerm (Term (PiT v t1 t2) d1) typ = do
  s <- checkTermExpected t1 TyT
  _ <- enterCtxMod (addTyping v (sub s t1) False) $ inferTerm (sub s t2)
  unifyTerms typ (locatedAt d1 TyT)
checkTerm (Term (SigmaT v t1 t2) d1) typ = do
  s <- checkTermExpected t1 TyT
  _ <- enterCtxMod (addTyping v (sub s t1) False) $ inferTerm (sub s t2)
  unifyTerms typ (locatedAt d1 TyT)
checkTerm (Term TyT d1) typ = unifyTerms typ (Term TyT d1)
checkTerm (Term (V v) _) typ = do
  vTyp <- inCtx (lookupType v)
  case vTyp of
    Nothing -> do
      -- If we are in a pattern, then this is a bound variable so we can add it
      -- to the context.
      p <- inState inPat
      if p
        then do
          modifyCtx (addTyping v typ True)
          return noSub
        else throwError $ VariableNotFound v
    Just vTyp' -> case termValue typ of
      Hole h -> return $ Sub [(h, vTyp')]
      _ -> unifyTerms typ vTyp'
checkTerm (Term (App t1 t2) _) typ = do
  v <- freshHoleVar
  bodyTy <- freshHole
  varTy <- freshHole
  let expectedTy = locatedAt t1 (PiT v varTy bodyTy)
  s1 <- checkTerm t1 expectedTy
  let bodyTy' = sub s1 bodyTy
  let varTy' = sub s1 varTy

  s2 <- checkTerm t2 varTy'
  let t2' = sub (s1 <> s2) t2
  let bodyTy'' = sub s2 bodyTy'

  s3 <- unifyTerms typ (subVar v t2' bodyTy'')

  return (s1 <> s2 <> s3)
checkTerm (Term (Hole _) _) typ = do
  hTy <- freshHoleVar
  return $ Sub [(hTy, typ)]
checkTerm (Term (Global g) _) typ = do
  decl <- inGlobalCtx (lookupItemOrCtor g)
  case decl of
    Nothing -> throwError $ ItemNotFound g
    Just (Left (Decl decl')) -> unifyTerms typ $ declTy decl'
    Just (Left (Data dat)) -> unifyTerms typ $ dataTy dat
    Just (Right ctor) -> unifyTerms typ $ ctorItemTy ctor
checkTerm (Term Wild _) _ = return noSub

-- | Infer the type of a term and return the substitution.
inferTermWithSub :: Term -> Tc (Sub, Type)
inferTermWithSub t = do
  ty <- freshHole
  s <- checkTerm t ty
  return (s, sub s ty)

-- | Infer the type of a term.
inferTerm :: Term -> Tc Type
inferTerm t = snd <$> inferTermWithSub t

-- | Reduce a term to normal form (one step).
-- If this is not possible, return Nothing.
normaliseTerm :: Term -> Tc (Maybe Term)
normaliseTerm (Term (App (Term (Lam v t1) _) t2) _) = do
  return . Just $ subVar v t2 t1
normaliseTerm (Term (App t1 t2) d1) = do
  t1' <- normaliseTerm t1
  case t1' of
    Nothing -> return Nothing
    Just t1'' -> do
      return $ Just (Term (App t1'' t2) d1)
normaliseTerm _ = return Nothing -- TODO: normalise declarations

-- | Reduce a term to normal form (fully).
normaliseTermFully :: Term -> Tc Term
normaliseTermFully t = do
  t' <- normaliseTerm t
  case t' of
    Nothing -> return t
    Just t'' -> normaliseTermFully t''

-- | Unify two terms.
-- This might produce a substitution.
-- Unification is currently symmetric.
unifyTerms :: Term -> Term -> Tc Sub
unifyTerms (Term (PiT lv l1 l2) _) (Term (PiT rv r1 r2) _) = do
  s1 <- unifyTerms l1 r1
  s2 <- unifyTerms l2 (alphaRename rv lv r2)
  return $ s1 <> s2
unifyTerms (Term (SigmaT lv l1 l2) _) (Term (SigmaT rv r1 r2) _) = do
  s1 <- unifyTerms l1 r1
  s2 <- unifyTerms l2 (alphaRename rv lv r2)
  return $ s1 <> s2
unifyTerms (Term (Lam lv l) _) (Term (Lam rv r) _) = do
  unifyTerms l (alphaRename rv lv r)
unifyTerms (Term (Pair l1 l2) _) (Term (Pair r1 r2) _) = do
  s1 <- unifyTerms l1 r1
  s2 <- unifyTerms l2 r2
  return $ s1 <> s2
unifyTerms (Term TyT _) (Term TyT _) = return noSub
unifyTerms (Term (Hole l) _) (Term (Hole r) _)
  | l == r = return noSub
  | otherwise = throwError $ CannotUnifyTwoHoles l r
unifyTerms (Term (Hole h) _) b@(Term _ _) = do
  return $ Sub [(h, b)]
unifyTerms a@(Term _ _) (Term (Hole h) _) = do
  return $ Sub [(h, a)]
unifyTerms (Term (V l) _) (Term (V r) _) | l == r = return noSub
unifyTerms a@(Term (V v) _) b@(Term _ _) = do
  -- Pattern bindings can always be unified with.
  patBind <- inCtx (isPatBind v)
  p <- inState inPat
  if patBind == Just True && p
    then do
      return $ Sub [(v, b)]
    else throwError $ Mismatch a b
unifyTerms a@(Term _ _) b@(Term (V v) _) = do
  -- Pattern bindings can always be unified with.
  patBind <- inCtx (isPatBind v)
  p <- inState inPat
  if patBind == Just True && p
    then do
      return $ Sub [(v, a)]
    else throwError $ Mismatch b a
unifyTerms a@(Term (Global l) _) b@(Term (Global r) _) =
  if l == r
    then return noSub
    else normaliseAndUnifyTerms a b
unifyTerms a@(Term (App l1 l2) _) b@(Term (App r1 r2) _) =
  do
    s1 <- unifyTerms l1 r1
    s2 <- unifyTerms l2 r2
    return $ s1 <> s2
    `catchError` (\_ -> normaliseAndUnifyTerms a b)
unifyTerms l r = normaliseAndUnifyTerms l r

-- | Unify two terms and return the substituted left term
unifyToLeft :: Term -> Term -> Tc Term
unifyToLeft l r = do
  s <- unifyTerms l r
  return $ sub s l

-- | Unify two terms, normalising them first.
normaliseAndUnifyTerms :: Term -> Term -> Tc Sub
normaliseAndUnifyTerms l r = do
  l' <- normaliseTerm l
  case l' of
    Nothing -> do
      r' <- normaliseTerm r
      case r' of
        Nothing -> throwError $ Mismatch l r
        Just r'' -> unifyTerms l r''
    Just l'' -> do
      unifyTerms l'' r

-- | Ensure that a substitution is empty.
ensureEmptySub :: Sub -> Tc ()
ensureEmptySub (Sub []) = return ()
ensureEmptySub (Sub xs) = throwError $ NeedMoreTypeHints (map fst xs)

-- | Convert a pattern to a term, converting wildcards to fresh variables.
patToTerm :: Pat -> Tc Term
patToTerm =
  mapTermM
    ( \t -> case termValue t of
        Wild -> do
          v <- freshVar
          return . Just $ Term (V v) (termData t)
        _ -> return Nothing
    )
