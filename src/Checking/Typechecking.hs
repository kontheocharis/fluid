module Checking.Typechecking (checkTerm, unifyTerms, inferTerm, normaliseTermFully, checkProgram) where

import Checking.Context
  ( FlexApp (..),
    Tc,
    TcError (..),
    TcState (inPat, metaValues, termTypes),
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
    isPatBind,
    lookupItemOrCtor,
    lookupType,
    modifyCtx,
    modifyGlobalCtx,
    setType,
    solveMeta,
  )
import Checking.Vars (Sub (..), Subst (sub), alphaRename, subVar)
import Control.Monad (replicateM)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.State (get)
import Data.Bifunctor (second)
import Data.Map (Map, (!?))
import Debug.Trace (trace)
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
    TermMappable (mapTermMappableM),
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
  p' <- mapTermMappableM fillAllMetas p
  mapTermMappableM (fillType types) p'
  where
    fillType :: Map Loc Type -> Term -> Tc (MapResult Term)
    fillType types t = case types !? getLoc t of
      Just ty -> do
        ty' <- mapTermM fillAllMetas ty
        return $ ReplaceAndContinue (typedAs ty' t)
      Nothing -> return Continue

-- | Fill all the metavariables in a term.
fillAllMetas :: Term -> Tc (MapResult Term)
fillAllMetas t = ReplaceAndContinue <$> resolveShallow t

-- | Resolve a term by filling in metas if present.
resolveShallow :: Term -> Tc Term
resolveShallow (Term (Meta h) d) = do
  s <- get
  case metaValues s !? h of
    Just t -> resolveShallow t
    Nothing -> return $ Term (Meta h) d
resolveShallow (Term (App t1 t2) d) = do
  t1' <- resolveShallow t1
  normaliseTermFully (Term (App t1' t2) d)
resolveShallow t = return t

-- | Check some item in the program.
checkItem :: Item -> Tc Item
checkItem (Decl decl) = Decl <$> checkDeclItem decl
checkItem (Data dat) = Data <$> checkDataItem dat

-- | Check a data item.
checkDataItem :: DataItem -> Tc DataItem
checkDataItem (DataItem name ty ctors) = do
  -- Check the signature of the data type.
  (ty', _) <- checkTerm ty (locatedAt ty TyT)
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
  (ty', _) <- checkTerm ty (genTerm TyT)
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
  (ty', _) <- checkTerm ty (genTerm TyT)

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
  (r', _) <- checkTerm r t
  return (Clause [] r')
checkClause ((v, a) : as, t) (Clause (p : ps) r) = do
  pt <- patToTerm p
  (pt', _) <- enterPat $ checkTerm pt a
  let s' = Sub [(v, pt')]
  c <- checkClause (map (second (sub s')) as, sub s' t) (Clause ps r)
  return $ prependPatToClause p c
checkClause ([], _) cl@(Clause (p : _) _) = throwError $ TooManyPatterns cl p
checkClause ((_, t) : _, _) cl@(Clause [] _) = throwError $ TooFewPatterns cl t
checkClause _ (ImpossibleClause _) = error "Impossible clauses not yet supported"

-- | Check the type of a term, and set the type in the context.
checkTerm :: Term -> Type -> Tc (Term, Type)
checkTerm v t = do
  (v', t') <- checkTerm' v t
  setType v' t'
  return (v', t')

-- | Check the type of a term.
--
-- The location of the type is inherited from the term.
checkTermExpected :: Term -> TypeValue -> Tc (Term, Type)
checkTermExpected v t = checkTerm v (locatedAt v t)

-- | Unify two terms and return the first one.
unifyTermsTo :: Term -> Term -> Tc Term
unifyTermsTo t1 t2 = do
  unifyTerms t1 t2
  return t1

-- | Check the type of a term. (The type itself should already be checked.)
--
-- This also performs elaboration by filling named holes and wildcards with metavariables.
checkTerm' :: Term -> Type -> Tc (Term, Type)
checkTerm' ((Term (Lam v t) d1)) ((Term (PiT var' ty1 ty2) d2)) = do
  (t', ty2') <- enterCtxMod (addTyping v ty1 False) $ checkTerm t (alphaRename var' (v, d2) ty2)
  return (locatedAt d1 (Lam v t'), locatedAt d2 (PiT var' ty1 ty2'))
checkTerm' ((Term (Lam v t1) d1)) typ = do
  varTy <- freshMeta
  (t1', bodyTy) <- enterCtxMod (addTyping v varTy False) $ inferTerm t1
  typ' <- unifyTermsTo typ $ locatedAt d1 (PiT v varTy bodyTy)
  return (locatedAt d1 (Lam v t1'), typ')
checkTerm' (Term (Pair t1 t2) d1) (Term (SigmaT v ty1 ty2) d2) = do
  (t1', ty1') <- checkTerm t1 ty1
  (t2', ty2') <- checkTerm t2 (subVar v t1 ty2)
  return (locatedAt d1 (Pair t1' t2'), locatedAt d2 (SigmaT v ty1' ty2'))
checkTerm' (Term (Pair t1 t2) d1) typ = do
  (t1', ty1) <- inferTerm t1
  (t2', ty2) <- inferTerm t2
  v <- freshVar
  typ' <- unifyTermsTo typ $ locatedAt d1 (SigmaT v ty1 ty2)
  return (locatedAt d1 (Pair t1' t2'), typ')
checkTerm' (Term (PiT v t1 t2) d1) typ = do
  (t1', _) <- checkTermExpected t1 TyT
  (t2', _) <- enterCtxMod (addTyping v t1 False) $ checkTermExpected t2 TyT
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (locatedAt d1 (PiT v t1' t2'), typ')
checkTerm' (Term (SigmaT v t1 t2) d1) typ = do
  (t1', _) <- checkTermExpected t1 TyT
  (t2', _) <- enterCtxMod (addTyping v t1 False) $ checkTermExpected t2 TyT
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (locatedAt d1 (SigmaT v t1' t2'), typ')
checkTerm' (Term TyT d1) typ = do
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (Term TyT d1, typ')
checkTerm' (Term NatT d1) typ = do
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (Term NatT d1, typ')
checkTerm' (Term (ListT t) d1) typ = do
  (t', _) <- checkTermExpected t TyT
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (locatedAt d1 (ListT t'), typ')
checkTerm' (Term (VectT t n) d1) typ = do
  (t', _) <- checkTermExpected t TyT
  (n', _) <- checkTermExpected n NatT
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (locatedAt d1 (VectT t' n'), typ')
checkTerm' (Term (FinT t) d1) typ = do
  (t', _) <- checkTermExpected t NatT
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (locatedAt d1 (FinT t'), typ')
checkTerm' (Term (EqT t1 t2) d1) typ = do
  (t1', ty1) <- inferTerm t1
  (t2', ty2) <- inferTerm t2
  _ <- unifyTermsTo ty1 ty2
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (locatedAt d1 (EqT t1' t2'), typ')
checkTerm' (Term (LteT t1 t2) d1) typ = do
  _ <- checkTermExpected t1 NatT
  _ <- checkTermExpected t2 NatT
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (locatedAt d1 (LteT t1 t2), typ')
checkTerm' (Term (MaybeT t) d1) typ = do
  (t', _) <- checkTermExpected t TyT
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (locatedAt d1 (MaybeT t'), typ')
checkTerm' t@(Term (V v) _) typ = do
  vTyp <- inCtx (lookupType v)
  case vTyp of
    Nothing -> do
      -- If we are in a pattern, then this is a bound variable so we can add it
      -- to the context.
      p <- inState inPat
      if p
        then do
          modifyCtx (addTyping v typ True)
          return (t, typ)
        else throwError $ VariableNotFound v
    Just vTyp' -> do
      typ' <- unifyTermsTo typ vTyp'
      return (t, typ')
checkTerm' (Term (App t1 t2) _) typ = do
  (t1', subjectTy) <- inferTerm t1
  subjectTyRes <- resolveShallow subjectTy

  let go v varTy bodyTy = do
        (t2', _) <- checkTerm t2 varTy
        typ' <- unifyTermsTo typ $ subVar v t2' bodyTy
        return (locatedAt t1 (App t1' t2'), typ')

  -- Try to normalise to a pi type.
  case subjectTyRes of
    (Term (PiT v varTy bodyTy) _) -> go v varTy bodyTy
    _ -> do
      subjectTy' <- normaliseTerm subjectTyRes
      subjectTyRes' <- case subjectTy' of
        Just t -> Just <$> resolveShallow t
        Nothing -> return Nothing
      case subjectTyRes' of
        Just (Term (PiT v varTy bodyTy) _) -> go v varTy bodyTy
        _ -> throwError $ NotAFunction subjectTy
checkTerm' t@(Term (Global g) _) typ = do
  decl <- inGlobalCtx (lookupItemOrCtor g)
  case decl of
    Nothing -> throwError $ ItemNotFound g
    Just (Left (Decl decl')) -> do
      typ' <- unifyTermsTo typ $ declTy decl'
      return (t, typ')
    Just (Left (Data dat)) -> do
      typ' <- unifyTermsTo typ $ dataTy dat
      return (t, typ')
    Just (Right ctor) -> do
      typ' <- unifyTermsTo typ $ ctorItemTy ctor
      return (t, typ')
checkTerm' (Term (Case s cs) _) typ = do
  (s', sTy) <- inferTerm s
  cs' <-
    mapM
      ( \(p, t) -> enterCtx $ do
          pt <- patToTerm p
          (pt', _) <- enterPat $ checkTerm pt sTy
          (t', _) <- checkTerm t typ
          return (pt', t')
      )
      cs
  return (locatedAt s (Case s' cs'), typ)
checkTerm' (Term (Refl t) d1) typ = do
  ty <- freshMeta
  (t', typ') <- checkCtor1 ty (locatedAt d1 (EqT t t)) t typ
  return (locatedAt d1 (Refl t'), typ')
checkTerm' (Term Z d1) typ = do
  typ' <- checkCtor0 (locatedAt d1 NatT) typ
  return (Term Z d1, typ')
checkTerm' (Term (S n) d1) typ = do
  (n', typ') <- checkCtor1 (genTerm NatT) (locatedAt d1 NatT) n typ
  return (locatedAt d1 (S n'), typ')
checkTerm' (Term LNil d1) typ = do
  ty <- freshMeta
  typ' <- checkCtor0 (locatedAt d1 (ListT ty)) typ
  return (Term LNil d1, typ')
checkTerm' (Term (LCons h t) d1) typ = do
  ty <- freshMeta
  ((h', t'), typ') <- checkCtor2 (ty, genTerm (ListT ty)) (locatedAt d1 (ListT ty)) (h, t) typ
  return (locatedAt d1 (LCons h' t'), typ')
checkTerm' (Term (MJust t) d1) typ = do
  ty <- freshMeta
  (t', typ') <- checkCtor1 ty (locatedAt d1 (MaybeT ty)) t typ
  return (locatedAt d1 (MJust t'), typ')
checkTerm' (Term MNothing d1) typ = do
  ty <- freshMeta
  typ' <- checkCtor0 (locatedAt d1 (MaybeT ty)) typ
  return (Term MNothing d1, typ')
checkTerm' (Term LTEZero d1) typ = do
  right <- freshMeta
  typ' <- checkCtor0 (locatedAt d1 (LteT (locatedAt d1 Z) right)) typ
  return (Term LTEZero d1, typ')
checkTerm' (Term (LTESucc t) d1) typ = do
  left <- freshMeta
  right <- freshMeta
  (t', typ') <- checkCtor1 (genTerm (LteT left right)) (locatedAt d1 (LteT (locatedAt t (S left)) (locatedAt t (S right)))) t typ
  return (locatedAt d1 (LTESucc t'), typ')
checkTerm' (Term FZ d1) typ = do
  n <- freshMeta
  typ' <- checkCtor0 (locatedAt d1 (FinT (locatedAt d1 (S n)))) typ
  return (Term FZ d1, typ')
checkTerm' (Term (FS t) d1) typ = do
  n <- freshMeta
  (t', typ') <- checkCtor1 (genTerm (FinT n)) (locatedAt d1 (FinT (locatedAt t (S n)))) t typ
  return (locatedAt d1 (FS t'), typ')
checkTerm' (Term VNil d1) typ = do
  ty <- freshMeta
  typ' <- checkCtor0 (locatedAt d1 (VectT ty (locatedAt d1 Z))) typ
  return (Term VNil d1, typ')
checkTerm' (Term (VCons t1 t2) d1) typ = do
  n <- freshMeta
  ty <- freshMeta
  ((t1', t2'), typ') <- checkCtor2 (ty, genTerm (VectT ty n)) (locatedAt d1 (VectT ty (locatedAt t2 (S n)))) (t1, t2) typ
  return (locatedAt d1 (VCons t1' t2'), typ')

-- Wild and hole are turned into metavars:
checkTerm' (Term Wild _) typ = do
  m <- freshMeta
  return (m, typ)
checkTerm' (Term (Hole _) _) typ = do
  m <- freshMeta
  return (m, typ) -- @@Enhancement: retain the hole name in the meta?
checkTerm' t@(Term (Meta _) _) typ = error $ "Found metavar during checking: " ++ show t ++ " : " ++ show typ

-- @@Enhancement(kontheocharis):
-- I really dislike the presence of primitives here--they take up 90% of the space.
-- They should be in a prelude instead. Implement implicit arguments already!

-- | Check the type of a constructor (arity 2).
checkCtor2 :: (Type, Type) -> Type -> (Term, Term) -> Type -> Tc ((Term, Term), Type)
checkCtor2 (ty1, ty2) ctorRet (arg1, arg2) typ = do
  (arg1', _) <- checkTerm arg1 ty1
  (arg2', _) <- checkTerm arg2 ty2
  typ' <- unifyTermsTo typ ctorRet
  return ((arg1', arg2'), typ')

-- | Check the type of a constructor (arity 1).
checkCtor1 :: Type -> Type -> Term -> Type -> Tc (Term, Type)
checkCtor1 ty ctorRet arg typ = do
  (arg', _) <- checkTerm arg ty
  typ' <- unifyTermsTo typ ctorRet
  return (arg', typ')

-- | Check the type of a constructor (arity 0).
checkCtor0 :: Type -> Type -> Tc Type
checkCtor0 ctorRet typ = unifyTermsTo typ ctorRet

-- | Infer the type of a term.
inferTerm :: Term -> Tc (Term, Type)
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
normaliseTerm _ = return Nothing -- @@Todo: normalise declarations

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
  trace ("Unifying " ++ show a ++ " with " ++ show b) $ return ()
  case (classifyApp a, classifyApp b) of
    (Just (Flex v1 _), Just (Flex v2 _)) | v1 == v2 -> unifyTerms' a b
    (Just (Flex h1 ts1), _) -> solve h1 ts1 b
    (_, Just (Flex h2 ts2)) -> solve h2 ts2 a
    _ -> unifyTerms' a b
  where
    unifyTerms' :: Term -> Term -> Tc ()
    unifyTerms' (Term (PiT lv l1 l2) d1) (Term (PiT rv r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 (alphaRename rv (lv, d1) r2)
    unifyTerms' (Term (SigmaT lv l1 l2) d1) (Term (SigmaT rv r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 (alphaRename rv (lv, d1) r2)
    unifyTerms' (Term (Lam lv l) d1) (Term (Lam rv r) _) = do
      unifyTerms l (alphaRename rv (lv, d1) r)
    unifyTerms' (Term (Pair l1 l2) _) (Term (Pair r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 r2
    unifyTerms' (Term TyT _) (Term TyT _) = return ()
    unifyTerms' (Term (V l) _) (Term (V r) _) | l == r = return ()
    unifyTerms' a@(Term (V l) _) b = do
      pt <- inCtx (isPatBind l)
      case pt of
        Just True -> do
          modifyCtx (sub (Sub [(l, b)]))
        _ -> throwError $ Mismatch a b
    unifyTerms' a b@(Term (V l) _) = do
      pt <- inCtx (isPatBind l)
      case pt of
        Just True -> do
          modifyCtx (sub (Sub [(l, a)]))
        _ -> throwError $ Mismatch a b
    unifyTerms' a@(Term (Global l) _) b@(Term (Global r) _) =
      if l == r
        then return ()
        else normaliseAndUnifyTerms a b
    unifyTerms' (Term (Case su1 cs1) _) (Term (Case su2 cs2) _) = do
      unifyTerms su1 su2
      mapM_
        ( \((p1, t1), (p2, t2)) -> do
            unifyTerms p1 p2
            unifyTerms t1 t2
        )
        (zip cs1 cs2)
    unifyTerms' (Term NatT _) (Term NatT _) = return ()
    unifyTerms' (Term (ListT t) _) (Term (ListT r) _) = do
      unifyTerms t r
    unifyTerms' (Term (MaybeT t) _) (Term (MaybeT r) _) = do
      unifyTerms t r
    unifyTerms' (Term (VectT lt ln) _) (Term (VectT rt rn) _) = do
      unifyTerms lt rt
      unifyTerms ln rn
    unifyTerms' (Term (FinT l) _) (Term (FinT r) _) = do
      unifyTerms l r
    unifyTerms' (Term (EqT l1 l2) _) (Term (EqT r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 r2
    unifyTerms' (Term (LteT l1 l2) _) (Term (LteT r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 r2
    unifyTerms' (Term FZ _) (Term FZ _) = return ()
    unifyTerms' (Term (FS l) _) (Term (FS r) _) = do
      unifyTerms l r
    unifyTerms' (Term Z _) (Term Z _) = return ()
    unifyTerms' (Term (S l) _) (Term (S r) _) = do
      unifyTerms l r
    unifyTerms' (Term LNil _) (Term LNil _) = return ()
    unifyTerms' (Term (LCons l1 l2) _) (Term (LCons r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 r2
    unifyTerms' (Term VNil _) (Term VNil _) = return ()
    unifyTerms' (Term (VCons l1 l2) _) (Term (VCons r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 r2
    unifyTerms' (Term (MJust l) _) (Term (MJust r) _) = do
      unifyTerms l r
    unifyTerms' (Term MNothing _) (Term MNothing _) = return ()
    unifyTerms' (Term (Refl l) _) (Term (Refl r) _) = do
      unifyTerms l r
    unifyTerms' (Term LTEZero _) (Term LTEZero _) = return ()
    unifyTerms' (Term (LTESucc l) _) (Term (LTESucc r) _) = do
      unifyTerms l r
    unifyTerms' a@(Term (App l1 l2) _) b@(Term (App r1 r2) _) =
      do
        unifyTerms l1 r1
        unifyTerms l2 r2
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
