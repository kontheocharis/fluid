{-# LANGUAGE LambdaCase #-}

module Checking.Typechecking (checkTerm, unifyTerms, inferTerm, normaliseTermFully, checkProgram) where

import Checking.Context
  ( FlexApp (..),
    Tc,
    TcError (..),
    TcState (inPat, termTypes),
    addItem,
    addTyping,
    classifyApp,
    enterCtx,
    enterCtxMod,
    enterGlobalCtxMod,
    enterPat,
    freshMeta,
    freshVar,
    inCtx,
    inGlobalCtx,
    inState,
    lookupItemOrCtor,
    lookupType,
    modifyCtx,
    modifyGlobalCtx,
    resolveShallow,
    setType,
    solveMeta,
  )
import Checking.Vars (Sub (..), Subst (sub), alphaRename, subVar)
import Control.Monad (replicateM)
import Control.Monad.Except (catchError, throwError)
import Data.Bifunctor (second)
import Data.Map (Map, (!?))
import Lang
  ( Clause (..),
    CtorItem (..),
    DataItem (..),
    DeclItem (..),
    HasLoc (..),
    Item (..),
    Loc,
    MapResult (..),
    Pat,
    Program (..),
    Term (..),
    TermMappable (mapTermMappable),
    TermValue (..),
    Type,
    TypeValue,
    Var,
    genTerm,
    lams,
    listToApp,
    locatedAt,
    mapTermM,
    piTypeToList,
    prependPatToClause,
    typedAs,
  )

-- | Check the program
checkProgram :: Program -> Tc Program
checkProgram (Program decls) = do
  p <- Program <$> mapM checkItem decls
  types <- inState termTypes
  return $ mapTermMappable (fillType types) p
  where
    fillType :: Map Loc Type -> Term -> MapResult Term
    fillType types t = case types !? getLoc t of
      Just ty -> ReplaceAndContinue $ typedAs ty t
      Nothing -> Continue

-- trace (show types) $ return p

-- | Check some item in the program.
checkItem :: Item -> Tc Item
checkItem (Decl decl) = Decl <$> checkDeclItem decl
checkItem (Data dat) = Data <$> checkDataItem dat

-- | Check a data item.
checkDataItem :: DataItem -> Tc DataItem
checkDataItem (DataItem name ty ctors) = do
  -- Check the signature of the data type.
  ty' <- checkTerm ty (locatedAt ty TyT)
  let (_, ret) = piTypeToList ty'
  unifyTerms ret (locatedAt ret TyT)

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
  ty' <- checkTerm ty (genTerm TyT)
  let (tys, ret) = piTypeToList ty'

  -- \| Add all the arguments to the context
  enterCtxMod (\c -> foldr (\(v, t) c' -> addTyping v t False c') c tys) $ do
    -- \| Check that the return type is the data type.
    dummyArgs <- replicateM dTyArgCount freshMeta
    let dummyRet = listToApp (genTerm (Global dTyName), dummyArgs)
    unifyTerms ret dummyRet

  return (CtorItem name ty' dTyName)

-- | Check a declaration.
-- This is self-contained, so it does not produce a substitution.
checkDeclItem :: DeclItem -> Tc DeclItem
checkDeclItem decl = do
  -- First, check the type of the declaration.
  let ty = declTy decl
  _ <- checkTerm ty (genTerm TyT)

  -- Substitute the type.
  let tys = piTypeToList ty
  let decl' = decl {declTy = ty}

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
  _ <- checkTerm r t
  return (Clause [] r)
checkClause ((v, a) : as, t) (Clause (p : ps) r) = do
  pt <- patToTerm p
  _ <- enterPat $ checkTerm pt a
  -- let instantiatedPat = sub s pt
  let s' = Sub [(v, pt)]
  c <- checkClause (map (second (sub s')) as, sub s' t) (Clause ps r)
  return $ prependPatToClause p c
checkClause ([], _) cl@(Clause (p : _) _) = throwError $ TooManyPatterns cl p
checkClause ((_, t) : _, _) cl@(Clause [] _) = throwError $ TooFewPatterns cl t
checkClause _ (ImpossibleClause _) = error "Impossible clauses not yet supported"

-- | Check the type of a term, and set the type in the context.
checkTerm :: Term -> Type -> Tc Type
checkTerm v t = do
  t' <- checkTerm' v t
  setType v t'
  return t'

-- | Check the type of a term.
--
-- The location of the type is inherited from the term.
checkTermExpected :: Term -> TypeValue -> Tc Type
checkTermExpected v t = checkTerm v (locatedAt v t)

-- | Unify two terms and resolve the holes.
unifyTermsAndResolve :: Term -> Term -> Tc Term
unifyTermsAndResolve t1 t2 = do
  unifyTerms t1 t2
  resolveShallow t1

-- | Check the type of a term. (The type itself should already be checked.)
-- This might produce a substitution.
checkTerm' :: Term -> Type -> Tc Type
checkTerm' ((Term (Lam v t) _)) ((Term (PiT var' ty1 ty2) d2)) = do
  ty2' <- enterCtxMod (addTyping v ty1 False) $ checkTerm t (alphaRename var' (v, d2) ty2)
  return $ locatedAt d2 (PiT var' ty1 ty2')
checkTerm' ((Term (Lam v t1) d1)) typ = do
  varTy <- freshMeta
  bodyTy <- enterCtxMod (addTyping v varTy False) $ inferTerm t1
  unifyTermsAndResolve typ $ locatedAt d1 (PiT v varTy bodyTy)
checkTerm' (Term (Pair t1 t2) _) (Term (SigmaT v ty1 ty2) d2) = do
  ty1' <- checkTerm t1 ty1
  ty2' <- checkTerm t2 (subVar v t1 ty2)
  return $ locatedAt d2 (SigmaT v ty1' ty2')
checkTerm' (Term (Pair t1 t2) d1) typ = do
  t1' <- inferTerm t1
  t2' <- inferTerm t2
  v <- freshVar
  unifyTermsAndResolve typ $ locatedAt d1 (SigmaT v t1' t2')
checkTerm' (Term (PiT v t1 t2) d1) typ = do
  _ <- checkTermExpected t1 TyT
  _ <- enterCtxMod (addTyping v t1 False) $ checkTermExpected t2 TyT
  unifyTermsAndResolve typ $ locatedAt d1 TyT
checkTerm' (Term (SigmaT v t1 t2) d1) typ = do
  _ <- checkTermExpected t1 TyT
  _ <- enterCtxMod (addTyping v t1 False) $ checkTermExpected t2 TyT
  unifyTermsAndResolve typ (locatedAt d1 TyT)
checkTerm' (Term TyT d1) typ = unifyTermsAndResolve typ (Term TyT d1)
checkTerm' (Term NatT d1) typ = unifyTermsAndResolve typ (Term TyT d1)
checkTerm' (Term (ListT t) d1) typ = do
  _ <- checkTermExpected t TyT
  unifyTermsAndResolve typ (locatedAt d1 TyT)
checkTerm' (Term (VectT t n) d1) typ = do
  _ <- checkTermExpected t TyT
  _ <- checkTermExpected n NatT
  unifyTermsAndResolve typ (Term TyT d1)
checkTerm' (Term (FinT t) d1) typ = do
  _ <- checkTermExpected t NatT
  unifyTermsAndResolve typ (Term TyT d1)
checkTerm' (Term (EqT t1 t2) d1) typ = do
  ty1 <- inferTerm t1
  ty2 <- inferTerm t2
  _ <- unifyTermsAndResolve ty1 ty2
  unifyTermsAndResolve typ (Term TyT d1)
checkTerm' (Term (LteT t1 t2) d1) typ = do
  _ <- checkTermExpected t1 NatT
  _ <- checkTermExpected t2 NatT
  unifyTermsAndResolve typ (Term TyT d1)
checkTerm' (Term (MaybeT t) d1) typ = do
  _ <- checkTermExpected t TyT
  unifyTermsAndResolve typ (Term TyT d1)
checkTerm' (Term (V v) _) typ = do
  vTyp <- inCtx (lookupType v)
  case vTyp of
    Nothing -> do
      -- If we are in a pattern, then this is a bound variable so we can add it
      -- to the context.
      p <- inState inPat
      if p
        then do
          modifyCtx (addTyping v typ True)
          return typ
        else throwError $ VariableNotFound v
    Just vTyp' -> unifyTermsAndResolve typ vTyp'
checkTerm' (Term (App t1 t2) _) typ = do
  varTy <- freshMeta
  bodyTy <- freshMeta
  v <- freshVar
  let inferredTy = locatedAt t1 (PiT v varTy bodyTy)
  _ <- checkTerm t1 inferredTy
  unifyTermsAndResolve typ $ subVar v t2 bodyTy
checkTerm' (Term (Global g) _) typ = do
  decl <- inGlobalCtx (lookupItemOrCtor g)
  case decl of
    Nothing -> throwError $ ItemNotFound g
    Just (Left (Decl decl')) -> unifyTermsAndResolve typ $ declTy decl'
    Just (Left (Data dat)) -> unifyTermsAndResolve typ $ dataTy dat
    Just (Right ctor) -> unifyTermsAndResolve typ $ ctorItemTy ctor
checkTerm' (Term (Case s cs) _) typ = do
  sTy <- inferTerm s
  mapM_
    ( \(p, t) -> enterCtx $ do
        _ <- enterPat $ checkTerm p sTy
        _ <- checkTerm t typ
        return ()
    )
    cs
  return typ
checkTerm' (Term (Refl t) d1) typ = do
  ty <- freshMeta
  checkCtor [ty] [ty] (locatedAt d1 (EqT t t)) [t] typ
checkTerm' (Term Z d1) typ = do
  checkCtor [] [] (locatedAt d1 NatT) [] typ
checkTerm' (Term (S n) d1) typ = do
  checkCtor [] [genTerm NatT] (locatedAt d1 NatT) [n] typ
checkTerm' (Term LNil d1) typ = do
  ty <- freshMeta
  checkCtor [ty] [] (locatedAt d1 (ListT ty)) [] typ
checkTerm' (Term (LCons h t) d1) typ = do
  ty <- freshMeta
  checkCtor [ty] [ty, genTerm (ListT ty)] (locatedAt d1 (ListT ty)) [h, t] typ
checkTerm' (Term (MJust t) d1) typ = do
  ty <- freshMeta
  checkCtor [ty] [ty] (locatedAt d1 (MaybeT ty)) [t] typ
checkTerm' (Term MNothing d1) typ = do
  ty <- freshMeta
  checkCtor [ty] [] (locatedAt d1 (MaybeT ty)) [] typ
checkTerm' (Term LTEZero d1) typ = do
  right <- freshMeta
  checkCtor [right] [] (locatedAt d1 (LteT (locatedAt d1 Z) right)) [] typ
checkTerm' (Term (LTESucc t) d1) typ = do
  left <- freshMeta
  right <- freshMeta
  checkCtor
    [left, right]
    [genTerm (LteT left right)]
    (locatedAt d1 (LteT (locatedAt t (S left)) (locatedAt t (S right))))
    [t]
    typ
checkTerm' (Term FZ d1) typ = do
  n <- freshMeta
  checkCtor [n] [] (locatedAt d1 (FinT (locatedAt d1 (S n)))) [] typ
checkTerm' (Term (FS t) d1) typ = do
  n <- freshMeta
  checkCtor [n] [genTerm (FinT n)] (locatedAt d1 (FinT (locatedAt t (S n)))) [t] typ
checkTerm' (Term VNil d1) typ = do
  ty <- freshMeta
  checkCtor [ty] [] (locatedAt d1 (VectT ty (locatedAt d1 Z))) [] typ
checkTerm' (Term (VCons t1 t2) d1) typ = do
  n <- freshMeta
  ty <- freshMeta
  checkCtor
    [n, ty]
    [ty, genTerm (VectT ty n)]
    (locatedAt d1 (VectT ty (locatedAt t2 (S n))))
    [t1, t2]
    typ

-- Wild and hole are turned into metavars:
checkTerm' (Term Wild _) typ = return typ
checkTerm' (Term (Meta _) _) typ = return typ
checkTerm' (Term (Hole _) _) typ = do
  hTy <- freshMeta
  unifyTermsAndResolve typ hTy

-- | Check the type of a constructor.
checkCtor :: [Term] -> [Type] -> Type -> [Term] -> Type -> Tc Type
checkCtor _ ctorParams ctorRet ctorArgs annotType = do
  mapM_ (\(ty, arg) -> checkTerm arg ty) (zip ctorParams ctorArgs)
  unifyTermsAndResolve annotType ctorRet

-- | Infer the type of a term.
inferTerm :: Term -> Tc Type
inferTerm t = do
  ty <- freshMeta
  checkTerm t ty

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

-- \| Unify two terms.
-- This might produce a substitution.
-- Unification is symmetric.
unifyTerms :: Term -> Term -> Tc ()
unifyTerms a' b' = do
  a <- resolveShallow a'
  b <- resolveShallow b'
  case (classifyApp a, classifyApp b) of
    (Just (Flex v1 _), Just (Flex v2 _)) | v1 == v2 -> unifyTerms' a b
    (Just (Flex h1 ts1), _) -> solve h1 ts1 b
    (_, Just (Flex h2 ts2)) -> solve h2 ts2 a
    _ -> unifyTerms' a b
  where
    unifyTerms' :: Term -> Term -> Tc ()
    unifyTerms' (Term (PiT lv l1 l2) d1) (Term (PiT rv r1 r2) _) = do
      unifyTerms' l1 r1
      unifyTerms' l2 (alphaRename rv (lv, d1) r2)
    unifyTerms' (Term (SigmaT lv l1 l2) d1) (Term (SigmaT rv r1 r2) _) = do
      unifyTerms' l1 r1
      unifyTerms' l2 (alphaRename rv (lv, d1) r2)
    unifyTerms' (Term (Lam lv l) d1) (Term (Lam rv r) _) = do
      unifyTerms' l (alphaRename rv (lv, d1) r)
    unifyTerms' (Term (Pair l1 l2) _) (Term (Pair r1 r2) _) = do
      unifyTerms' l1 r1
      unifyTerms' l2 r2
    unifyTerms' (Term TyT _) (Term TyT _) = return ()
    unifyTerms' (Term (V l) _) (Term (V r) _) | l == r = return ()
    unifyTerms' a@(Term (Global l) _) b@(Term (Global r) _) =
      if l == r
        then return ()
        else normaliseAndUnifyTerms a b
    unifyTerms' (Term (Case su1 cs1) _) (Term (Case su2 cs2) _) = do
      unifyTerms' su1 su2
      mapM_
        ( \((p1, t1), (p2, t2)) -> do
            unifyTerms' p1 p2
            unifyTerms' t1 t2
        )
        (zip cs1 cs2)
    unifyTerms' (Term NatT _) (Term NatT _) = return ()
    unifyTerms' (Term (ListT t) _) (Term (ListT r) _) = do
      unifyTerms' t r
    unifyTerms' (Term (MaybeT t) _) (Term (MaybeT r) _) = do
      unifyTerms' t r
    unifyTerms' (Term (VectT lt ln) _) (Term (VectT rt rn) _) = do
      unifyTerms' lt rt
      unifyTerms' ln rn
    unifyTerms' (Term (FinT l) _) (Term (FinT r) _) = do
      unifyTerms' l r
    unifyTerms' (Term (EqT l1 l2) _) (Term (EqT r1 r2) _) = do
      unifyTerms' l1 r1
      unifyTerms' l2 r2
    unifyTerms' (Term (LteT l1 l2) _) (Term (LteT r1 r2) _) = do
      unifyTerms' l1 r1
      unifyTerms' l2 r2
    unifyTerms' (Term FZ _) (Term FZ _) = return ()
    unifyTerms' (Term (FS l) _) (Term (FS r) _) = do
      unifyTerms' l r
    unifyTerms' (Term Z _) (Term Z _) = return ()
    unifyTerms' (Term (S l) _) (Term (S r) _) = do
      unifyTerms' l r
    unifyTerms' (Term LNil _) (Term LNil _) = return ()
    unifyTerms' (Term (LCons l1 l2) _) (Term (LCons r1 r2) _) = do
      unifyTerms' l1 r1
      unifyTerms' l2 r2
    unifyTerms' (Term VNil _) (Term VNil _) = return ()
    unifyTerms' (Term (VCons l1 l2) _) (Term (VCons r1 r2) _) = do
      unifyTerms' l1 r1
      unifyTerms' l2 r2
    unifyTerms' (Term (MJust l) _) (Term (MJust r) _) = do
      unifyTerms' l r
    unifyTerms' (Term MNothing _) (Term MNothing _) = return ()
    unifyTerms' (Term (Refl l) _) (Term (Refl r) _) = do
      unifyTerms' l r
    unifyTerms' (Term LTEZero _) (Term LTEZero _) = return ()
    unifyTerms' (Term (LTESucc l) _) (Term (LTESucc r) _) = do
      unifyTerms' l r
    unifyTerms' a@(Term (App l1 l2) _) b@(Term (App r1 r2) _) =
      do
        unifyTerms' l1 r1
        unifyTerms' l2 r2
        `catchError` (\_ -> normaliseAndUnifyTerms a b)
    unifyTerms' l r = normaliseAndUnifyTerms l r

-- | Unify two terms, normalising them first.
normaliseAndUnifyTerms :: Term -> Term -> Tc ()
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
          return . Replace $ Term (V v) (termData t)
        _ -> return Continue
    )

-- | Validate a pattern unification problem, returning the spine variables.
validateProb :: Var -> [Term] -> Term -> Tc [Var]
validateProb _ [] _ = return []
validateProb hole (x : xs) rhs = do
  x' <- resolveShallow x
  case termValue x' of
    V v -> do
      xs' <- validateProb hole xs rhs
      return $ v : xs'
    _ -> throwError $ Mismatch (genTerm (Hole hole)) rhs -- @@Todo : better error message

-- | Solve a pattern unification problem.
solve :: Var -> [Term] -> Term -> Tc ()
solve hole spine rhs = do
  vars <- validateProb hole spine rhs
  solution <- normaliseTermFully (lams vars rhs)
  solveMeta hole solution
