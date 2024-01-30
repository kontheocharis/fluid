{-# LANGUAGE LambdaCase #-}

module Checking.Typechecking (checkTerm, unifyTerms, inferTerm, normaliseTermFully, checkProgram) where

import Checking.Context
  ( Tc,
    TcError (..),
    TcState (inPat, termTypes),
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
    resolveShallow,
    setType,
    solveHole,
  )
import Checking.Vars (Sub (..), Subst (sub), alphaRename, noSub, subVar)
import Control.Monad (foldM, replicateM)
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
    dummyArgs <- replicateM dTyArgCount freshHole
    let dummyRet = listToApp (genTerm (Global dTyName), dummyArgs)
    unifyTerms ret dummyRet

  return (CtorItem name ty' dTyName)

-- | Check a declaration.
-- This is self-contained, so it does not produce a substitution.
checkDeclItem :: DeclItem -> Tc DeclItem
checkDeclItem decl = do
  -- First, check the type of the declaration.
  let ty = declTy decl
  ty' <- checkTerm ty (genTerm TyT)

  -- Substitute the type.
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
  varTy <- freshHole
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
  varTy <- freshHole
  bodyTy <- freshHole
  v <- freshHoleVar
  let inferredTy = locatedAt t1 (PiT v varTy bodyTy)
  _ <- checkTerm t1 inferredTy
  unifyTermsAndResolve typ $ subVar v t2 bodyTy
checkTerm' (Term (Hole _) _) typ = do
  hTy <- freshHole
  unifyTermsAndResolve typ hTy
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
  ty <- freshHoleVar
  checkCtor [ty] [V ty] (locatedAt d1 (EqT t t)) [t] typ
checkTerm' (Term Z d1) typ = do
  checkCtor [] [] (locatedAt d1 NatT) [] typ
checkTerm' (Term (S n) d1) typ = do
  checkCtor [] [NatT] (locatedAt d1 NatT) [n] typ
checkTerm' (Term LNil d1) typ = do
  ty <- freshHoleVar
  checkCtor [ty] [] (locatedAt d1 (ListT (genTerm (V ty)))) [] typ
checkTerm' (Term (LCons h t) d1) typ = do
  ty <- freshHoleVar
  checkCtor [ty] [V ty, ListT (locatedAt h (V ty))] (locatedAt d1 (ListT (locatedAt h (V ty)))) [h, t] typ
checkTerm' (Term (MJust t) d1) typ = do
  ty <- freshHoleVar
  checkCtor [ty] [V ty] (locatedAt d1 (MaybeT (locatedAt t (V ty)))) [t] typ
checkTerm' (Term MNothing d1) typ = do
  ty <- freshHoleVar
  checkCtor [ty] [] (locatedAt d1 (MaybeT (genTerm (V ty)))) [] typ
checkTerm' (Term LTEZero d1) typ = do
  right <- freshHoleVar
  checkCtor [right] [] (locatedAt d1 (LteT (locatedAt d1 Z) (locatedAt d1 (V right)))) [] typ
checkTerm' (Term (LTESucc t) d1) typ = do
  left <- freshHoleVar
  right <- freshHoleVar
  checkCtor
    [left, right]
    [LteT (locatedAt t (V left)) (locatedAt t (V right))]
    (locatedAt d1 (LteT (locatedAt t (S (locatedAt t (V left)))) (locatedAt t (S (locatedAt t (V right))))))
    [t]
    typ
checkTerm' (Term FZ d1) typ = do
  n <- freshHoleVar
  checkCtor [n] [] (locatedAt d1 (FinT (locatedAt d1 (S (locatedAt d1 (V n)))))) [] typ
checkTerm' (Term (FS t) d1) typ = do
  n <- freshHoleVar
  checkCtor [n] [FinT (locatedAt t (V n))] (locatedAt d1 (FinT (locatedAt t (S (locatedAt t (V n)))))) [t] typ
checkTerm' (Term VNil d1) typ = do
  ty <- freshHoleVar
  checkCtor [ty] [] (locatedAt d1 (VectT (locatedAt d1 (V ty)) (locatedAt d1 Z))) [] typ
checkTerm' (Term (VCons t1 t2) d1) typ = do
  n <- freshHoleVar
  ty <- freshHoleVar
  checkCtor
    [n, ty]
    [V ty, VectT (locatedAt t1 (V ty)) (locatedAt t2 (V n))]
    (locatedAt d1 (VectT (locatedAt t1 (V ty)) (locatedAt t2 (S (locatedAt t2 (V n))))))
    [t1, t2]
    typ
checkTerm' (Term Wild _) typ = return typ

-- | Check the type of a constructor.
checkCtor :: [Var] -> [TypeValue] -> Type -> [Term] -> Type -> Tc Type
checkCtor implicitVars ctorParams ctorRet ctorArgs annotType = do
  let implicitVarHoles = map (genTerm . Hole) implicitVars
  let implicitVarSub = Sub $ zip implicitVars implicitVarHoles
  let instantiatedCtorRet = sub implicitVarSub ctorRet
  mapM_
    (\(ty, arg) -> checkTerm arg ty)
    (zip (map (sub implicitVarSub . genTerm) ctorParams) ctorArgs)
  unifyTermsAndResolve annotType instantiatedCtorRet

-- | Infer the type of a term.
inferTerm :: Term -> Tc Type
inferTerm t = do
  ty <- freshHole
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

-- | Unify two terms.
-- This might produce a substitution.
-- Unification is currently symmetric.
--
-- This also accepts a list of "weak holes" to always unify with the other side,
-- even if the other side is a hole.
unifyTermsWH :: [Var] -> Term -> Term -> Tc ()
unifyTermsWH wh (Term (PiT lv l1 l2) d1) (Term (PiT rv r1 r2) _) = do
  unifyTermsWH wh l1 r1
  unifyTermsWH wh l2 (alphaRename rv (lv, d1) r2)
unifyTermsWH wh (Term (SigmaT lv l1 l2) d1) (Term (SigmaT rv r1 r2) _) = do
  unifyTermsWH wh l1 r1
  unifyTermsWH wh l2 (alphaRename rv (lv, d1) r2)
unifyTermsWH wh (Term (Lam lv l) d1) (Term (Lam rv r) _) = do
  unifyTermsWH wh l (alphaRename rv (lv, d1) r)
unifyTermsWH wh (Term (Pair l1 l2) _) (Term (Pair r1 r2) _) = do
  unifyTermsWH wh l1 r1
  unifyTermsWH wh l2 r2
unifyTermsWH _ (Term TyT _) (Term TyT _) = return ()
unifyTermsWH _ (Term (V l) _) (Term (V r) _) | l == r = return ()
unifyTermsWH wh a@(Term (Hole l) _) b@(Term (Hole r) _)
  | l == r = return ()
  -- Check for weak holes before refusing to unify.
  | l `elem` wh = solveHole l b
  | r `elem` wh = solveHole r a
  | otherwise = throwError $ CannotUnifyTwoHoles l r
unifyTermsWH _ (Term (Hole h) _) b@(Term _ _) = do
  solveHole h b
unifyTermsWH _ a@(Term _ _) (Term (Hole h) _) = do
  solveHole h a
unifyTermsWH _ a@(Term (V v) _) b@(Term _ _) = do
  -- Pattern bindings can always be unified with.
  patBind <- inCtx (isPatBind v)
  p <- inState inPat
  if patBind == Just True && p
    then do
      return ()
    else -- return $ Sub [(v, b)]
      throwError $ Mismatch a b
unifyTermsWH _ a@(Term _ _) b@(Term (V v) _) = do
  -- Pattern bindings can always be unified with.
  patBind <- inCtx (isPatBind v)
  p <- inState inPat
  if patBind == Just True && p
    then do
      return ()
    else -- return $ Sub [(v, a)]
      throwError $ Mismatch b a
unifyTermsWH wh a@(Term (Global l) _) b@(Term (Global r) _) =
  if l == r
    then return ()
    else normaliseAndUnifyTerms wh a b
unifyTermsWH wh (Term (Case su1 cs1) _) (Term (Case su2 cs2) _) = do
  s1 <- unifyTermsWH wh su1 su2
  s2 <-
    foldM
      ( \s ((p1, t1), (p2, t2)) -> do
          sp <- unifyTermsWH wh p1 p2
          st <- unifyTermsWH wh t1 t2
          return $ s <> sp <> st
      )
      s1
      (zip cs1 cs2)
  return (s1 <> s2)
unifyTermsWH _ (Term NatT _) (Term NatT _) = return ()
unifyTermsWH wh (Term (ListT t) _) (Term (ListT r) _) = do
  unifyTermsWH wh t r
unifyTermsWH wh (Term (MaybeT t) _) (Term (MaybeT r) _) = do
  unifyTermsWH wh t r
unifyTermsWH wh (Term (VectT lt ln) _) (Term (VectT rt rn) _) = do
  s1 <- unifyTermsWH wh lt rt
  s2 <- unifyTermsWH wh ln rn
  return $ s1 <> s2
unifyTermsWH wh (Term (FinT l) _) (Term (FinT r) _) = do
  unifyTermsWH wh l r
unifyTermsWH wh (Term (EqT l1 l2) _) (Term (EqT r1 r2) _) = do
  s1 <- unifyTermsWH wh l1 r1
  s2 <- unifyTermsWH wh l2 r2
  return $ s1 <> s2
unifyTermsWH wh (Term (LteT l1 l2) _) (Term (LteT r1 r2) _) = do
  s1 <- unifyTermsWH wh l1 r1
  s2 <- unifyTermsWH wh l2 r2
  return $ s1 <> s2
unifyTermsWH _ (Term FZ _) (Term FZ _) = return ()
unifyTermsWH wh (Term (FS l) _) (Term (FS r) _) = do
  unifyTermsWH wh l r
unifyTermsWH _ (Term Z _) (Term Z _) = return ()
unifyTermsWH wh (Term (S l) _) (Term (S r) _) = do
  unifyTermsWH wh l r
unifyTermsWH _ (Term LNil _) (Term LNil _) = return ()
unifyTermsWH wh (Term (LCons l1 l2) _) (Term (LCons r1 r2) _) = do
  s1 <- unifyTermsWH wh l1 r1
  s2 <- unifyTermsWH wh l2 r2
  return $ s1 <> s2
unifyTermsWH _ (Term VNil _) (Term VNil _) = return ()
unifyTermsWH wh (Term (VCons l1 l2) _) (Term (VCons r1 r2) _) = do
  s1 <- unifyTermsWH wh l1 r1
  s2 <- unifyTermsWH wh l2 r2
  return $ s1 <> s2
unifyTermsWH wh (Term (MJust l) _) (Term (MJust r) _) = do
  unifyTermsWH wh l r
unifyTermsWH _ (Term MNothing _) (Term MNothing _) = return ()
unifyTermsWH wh (Term (Refl l) _) (Term (Refl r) _) = do
  unifyTermsWH wh l r
unifyTermsWH _ (Term LTEZero _) (Term LTEZero _) = return ()
unifyTermsWH wh (Term (LTESucc l) _) (Term (LTESucc r) _) = do
  unifyTermsWH wh l r
unifyTermsWH wh a@(Term (App l1 l2) _) b@(Term (App r1 r2) _) =
  do
    s1 <- unifyTermsWH wh l1 r1
    s2 <- unifyTermsWH wh l2 r2
    return $ s1 <> s2
    `catchError` (\_ -> normaliseAndUnifyTerms wh a b)
unifyTermsWH wh l r = normaliseAndUnifyTerms wh l r

-- | Unify two terms.
unifyTerms :: Term -> Term -> Tc ()
unifyTerms = unifyTermsWH []

-- | Unify two terms, normalising them first.
normaliseAndUnifyTerms :: [Var] -> Term -> Term -> Tc ()
normaliseAndUnifyTerms wh l r = do
  l' <- normaliseTerm l
  case l' of
    Nothing -> do
      r' <- normaliseTerm r
      case r' of
        Nothing -> throwError $ Mismatch l r
        Just r'' -> unifyTermsWH wh l r''
    Just l'' -> do
      unifyTermsWH wh l'' r

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
  solveHole hole solution
