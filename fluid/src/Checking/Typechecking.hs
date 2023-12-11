module Checking.Typechecking
  ( checkTerm,
    unifyTerms,
    unifyToLeft,
    inferTerm,
    normaliseTermFully,
    checkProgram,
    runUntilFixpoint,
    substituteHolesIn,
  )
where

import Checking.Context
  ( NextProblem (..),
    Problem,
    Tc,
    TcError (..),
    TcState (holeCounter, inPat, resolvedHoles),
    addItem,
    addTyping,
    deferProblem,
    enterCtx,
    enterCtxMod,
    enterGlobalCtxMod,
    enterPat,
    freshHole,
    freshHoleVar,
    freshVar,
    inCtx,
    inGlobalCtx,
    inNextProblem,
    inState,
    isPatBind,
    lookupHole,
    lookupItemOrCtor,
    lookupType,
    modifyCtx,
    modifyGlobalCtx,
    pushProblem,
    remainingHoles,
    remainingProblems,
    resolveSub,
  )
import Checking.Vars (Sub (..), Subst (sub), alphaRename, noSub, subInM, subSize, subVar)
import Control.Monad (foldM, replicateM)
import Control.Monad.Except (catchError, throwError)
import Data.Bifunctor (second)
import Lang
  ( Clause (..),
    CtorItem (..),
    DataItem (..),
    DeclItem (..),
    Item (..),
    Pat (..),
    Program (..),
    Term (..),
    TermMappable,
    Type,
    Var,
    listToPiType,
    piTypeToList,
    prependPatToClause,
  )

-- | Substitute all holes in a term from the context.
substituteHolesIn :: (TermMappable a) => a -> Tc a
substituteHolesIn t = do
  s <- inState resolvedHoles
  subInM s t

-- | Run the typechecker on a job until there are no more problems.
runUntilFixpoint :: (TermMappable a) => Tc a -> Tc a
runUntilFixpoint job = do
  res <- job
  p <- remainingProblems
  if p == 0
    then substituteHolesIn res
    else do
      (nSubbed, seenProblems) <- runNextProblems 0 []
      case nSubbed of
        0 -> throwError $ CannotSolveProblems seenProblems
        _ -> runUntilFixpoint job
  where
    runNextProblems :: Int -> [Problem] -> Tc (Int, [Problem])
    runNextProblems nSubbed seenProblems = do
      result <- inNextProblem unifyTermsWH
      case result of
        NoNextProblem -> return (nSubbed, seenProblems)
        Success p s -> do
          resolveSub s
          runNextProblems (nSubbed + subSize s) (p : seenProblems)
        Failure p e -> do
          case e of
            CannotUnifyTwoHoles _ _ -> do
              runNextProblems nSubbed (p : seenProblems)
            _ -> throwError e

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
  s <- checkTerm ty TyT
  let (tys, ret) = piTypeToList (sub s ty)
  ret' <- unifyToLeft ret TyT
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
  s <- checkTerm ty TyT
  let ty' = sub s ty
  let (tys, ret) = piTypeToList ty'

  -- \| Add all the arguments to the context
  ret' <- enterCtxMod (\c -> foldr (\(v, t) c' -> addTyping v t False c') c tys) $ do
    -- \| Check that the return type is the data type.
    dummyArgs <- replicateM dTyArgCount freshHole
    let dummyRet = foldl App (Global dTyName) dummyArgs
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
  s1 <- checkTerm ty TyT

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

-- | Check the type of a term. (The type itself should already be checked.)
-- This might produce a substitution.
checkTerm :: Term -> Type -> Tc Sub
checkTerm (Lam v t) (PiT var' ty1 ty2) = do
  enterCtxMod (addTyping v ty1 False) $ checkTerm t (alphaRename var' v ty2)
checkTerm (Lam v t) typ = do
  varTy <- freshHole
  bodyTy <- enterCtxMod (addTyping v varTy False) $ inferTerm t
  let inferredTy = PiT v varTy bodyTy
  s1 <- unifyTerms typ inferredTy
  s2 <- checkTerm (sub s1 (Lam v t)) (sub s1 inferredTy)
  return $ s1 <> s2
checkTerm (Pair t1 t2) (SigmaT v ty1 ty2) = do
  s1 <- checkTerm t1 ty1
  s2 <- checkTerm (sub s1 t2) (subVar v (sub s1 t1) (sub s1 ty2))
  return $ s1 <> s2
checkTerm (Pair t1 t2) typ = do
  fstTy <- freshHole
  sndTy <- freshHole
  v <- freshVar
  let inferredTy = SigmaT v fstTy sndTy
  s1 <- checkTerm (Pair t1 t2) inferredTy
  s2 <- unifyTerms typ (sub s1 inferredTy)
  return $ s1 <> s2
checkTerm (PiT v t1 t2) typ = do
  s <- checkTerm t1 TyT
  _ <- enterCtxMod (addTyping v (sub s t1) False) $ inferTerm (sub s t2)
  unifyTerms typ TyT
checkTerm (SigmaT v t1 t2) typ = do
  s <- checkTerm t1 TyT
  _ <- enterCtxMod (addTyping v (sub s t1) False) $ inferTerm (sub s t2)
  unifyTerms typ TyT
checkTerm TyT typ = unifyTerms typ TyT
checkTerm NatT typ = unifyTerms typ TyT
checkTerm (ListT t) typ = do
  _ <- checkTerm t TyT
  unifyTerms typ TyT
checkTerm (VectT t n) typ = do
  _ <- checkTerm t TyT
  _ <- checkTerm n NatT
  unifyTerms typ TyT
checkTerm (FinT t) typ = do
  _ <- checkTerm t NatT
  unifyTerms typ TyT
checkTerm (EqT t1 t2) typ = do
  ty1 <- inferTerm t1
  ty2 <- inferTerm t2
  _ <- unifyTerms ty1 ty2
  unifyTerms typ TyT
checkTerm (LteT t1 t2) typ = do
  _ <- checkTerm t1 NatT
  _ <- checkTerm t2 NatT
  unifyTerms typ TyT
checkTerm (MaybeT t) typ = do
  _ <- checkTerm t TyT
  unifyTerms typ TyT
checkTerm (V v) typ = do
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
    Just vTyp' -> case typ of
      Hole h -> return $ Sub [(h, vTyp')]
      _ -> unifyTerms typ vTyp'
checkTerm (App t1 t2) typ = do
  bodyTy <- freshHole
  (s1, varTy) <- inferTermWithSub t2
  v <- freshHoleVar
  let inferredTy = PiT v varTy bodyTy
  s2 <- checkTerm (sub s1 t1) (sub s1 inferredTy)
  let s12 = s1 <> s2
  s3 <- unifyTerms (sub s12 typ) $ subVar v (sub s12 t2) (sub s12 bodyTy)
  return (s12 <> s3)
checkTerm (Hole h) ty = do
  hTerm <- lookupHole h
  case hTerm of
    Nothing -> do
      hTy <- freshHoleVar
      return $ Sub [(hTy, ty)]
    Just t -> checkTerm t ty
checkTerm (Global g) typ = do
  decl <- inGlobalCtx (lookupItemOrCtor g)
  case decl of
    Nothing -> throwError $ ItemNotFound g
    Just (Left (Decl decl')) -> unifyTerms typ $ declTy decl'
    Just (Left (Data dat)) -> unifyTerms typ $ dataTy dat
    Just (Right ctor) -> unifyTerms typ $ ctorItemTy ctor
checkTerm (Refl t) typ = do
  ty <- freshHoleVar
  checkCtor [ty] [V ty] (EqT t t) [t] typ
checkTerm Z typ = do
  checkCtor [] [] NatT [] typ
checkTerm (S n) typ = do
  checkCtor [] [NatT] NatT [n] typ
checkTerm LNil typ = do
  ty <- freshHoleVar
  checkCtor [ty] [] (ListT (V ty)) [] typ
checkTerm (LCons h t) typ = do
  ty <- freshHoleVar
  checkCtor [ty] [V ty, ListT (V ty)] (ListT (V ty)) [h, t] typ
checkTerm (MJust t) typ = do
  ty <- freshHoleVar
  checkCtor [ty] [V ty] (MaybeT (V ty)) [t] typ
checkTerm MNothing typ = do
  ty <- freshHoleVar
  checkCtor [ty] [] (MaybeT (V ty)) [] typ
checkTerm LTEZero typ = do
  right <- freshHoleVar
  checkCtor [right] [] (LteT Z (V right)) [] typ
checkTerm (LTESucc t) typ = do
  left <- freshHoleVar
  right <- freshHoleVar
  checkCtor [left, right] [LteT (V left) (V right)] (LteT (S (V left)) (S (V right))) [t] typ
checkTerm FZ typ = do
  n <- freshHoleVar
  checkCtor [n] [] (FinT (S (V n))) [] typ
checkTerm (FS t) typ = do
  n <- freshHoleVar
  checkCtor [n] [FinT (V n)] (FinT (S (V n))) [t] typ
checkTerm VNil typ = do
  ty <- freshHoleVar
  checkCtor [ty] [] (VectT (V ty) Z) [] typ
checkTerm (VCons t1 t2) typ = do
  n <- freshHoleVar
  ty <- freshHoleVar
  checkCtor [n, ty] [V ty, VectT (V ty) (V n)] (VectT (V ty) (S (V n))) [t1, t2] typ

-- | Check the type of a constructor.
checkCtor :: [Var] -> [Type] -> Type -> [Term] -> Type -> Tc Sub
checkCtor implicitVars ctorParams ctorRet ctorArgs annotType = do
  let implicitVarHoles = map Hole implicitVars
  let implicitVarSub = Sub $ zip implicitVars implicitVarHoles
  let instantiatedCtorRet = sub implicitVarSub ctorRet
  retSub <- unifyTermsWH implicitVars annotType instantiatedCtorRet
  foldM
    ( \ss (ty, arg) -> do
        s <- checkTerm arg (sub ss ty)
        return $ ss <> s
    )
    (implicitVarSub <> retSub)
    (zip ctorParams ctorArgs)

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
normaliseTerm (App (Lam v t1) t2) = do
  return . Just $ subVar v t2 t1
normaliseTerm (App t1 t2) = do
  t1' <- normaliseTerm t1
  case t1' of
    Nothing -> return Nothing
    Just t1'' -> do
      return . Just $ App t1'' t2
normaliseTerm _ = return Nothing -- TODO: normalise declarations

-- | Reduce a term to normal form (fully).
normaliseTermFully :: Term -> Tc Term
normaliseTermFully t = do
  t' <- normaliseTerm t
  case t' of
    Nothing -> return t
    Just t'' -> normaliseTermFully t''

-- | Unify two terms in place.
unifyTermsInPlace :: Term -> Term -> Tc ()
unifyTermsInPlace l r = do
  s1 <- unifyTerms l r
  resolveSub s1

-- | Unify two terms in place (with weak holes).
unifyTermsInPlaceWH :: [Var] -> Term -> Term -> Tc ()
unifyTermsInPlaceWH wh l r = do
  s1 <- unifyTermsWH wh l r
  resolveSub s1

-- | Unify two terms.
-- This might produce a substitution.
-- Unification is currently symmetric.
--
-- This also accepts a list of "weak holes" to always unify with the other side,
-- even if the other side is a hole.
unifyTermsWH :: [Var] -> Term -> Term -> Tc Sub
unifyTermsWH wh (PiT lv l1 l2) (PiT rv r1 r2) = do
  s1 <- unifyTermsWH wh l1 r1
  s2 <- unifyTermsWH wh l2 (alphaRename rv lv r2)
  return $ s1 <> s2
unifyTermsWH wh (SigmaT lv l1 l2) (SigmaT rv r1 r2) = do
  s1 <- unifyTermsWH wh l1 r1
  s2 <- unifyTermsWH wh l2 (alphaRename rv lv r2)
  return $ s1 <> s2
unifyTermsWH wh (Lam lv l) (Lam rv r) = do
  unifyTermsWH wh l (alphaRename rv lv r)
unifyTermsWH wh (Pair l1 l2) (Pair r1 r2) = do
  s1 <- unifyTermsWH wh l1 r1
  s2 <- unifyTermsWH wh l2 r2
  return $ s1 <> s2
unifyTermsWH _ TyT TyT = return noSub
unifyTermsWH wh (Hole l) (Hole r)
  | l == r = return noSub
  -- Check for weak holes before refusing to unify.
  | l `elem` wh = return $ Sub [(l, Hole r)]
  | r `elem` wh = return $ Sub [(r, Hole l)]
  | otherwise = throwError $ CannotUnifyTwoHoles l r
unifyTermsWH wh (Hole h) t = do
  hTerm <- lookupHole h
  case hTerm of
    Nothing -> do
      return $ Sub [(h, t)]
    Just t' -> unifyTermsWH wh t' t
unifyTermsWH wh t (Hole h) = do
  hTerm <- lookupHole h
  case hTerm of
    Nothing -> do
      return $ Sub [(h, t)]
    Just t' -> unifyTermsWH wh t t'
unifyTermsWH _ (V l) (V r) | l == r = return noSub
unifyTermsWH _ (V v) t = do
  -- Pattern bindings can always be unified with.
  patBind <- inCtx (isPatBind v)
  p <- inState inPat
  if patBind == Just True && p
    then do
      return $ Sub [(v, t)]
    else throwError $ Mismatch (V v) t
unifyTermsWH _ t (V v) = do
  -- Pattern bindings can always be unified with.
  patBind <- inCtx (isPatBind v)
  p <- inState inPat
  if patBind == Just True && p
    then do
      return $ Sub [(v, t)]
    else throwError $ Mismatch (V v) t
unifyTermsWH wh (Global l) (Global r) =
  if l == r
    then return noSub
    else normaliseAndUnifyTerms wh (Global l) (Global r)
unifyTermsWH _ NatT NatT = return noSub
unifyTermsWH wh (ListT t) (ListT r) = do
  unifyTermsWH wh t r
unifyTermsWH wh (MaybeT t) (MaybeT r) = do
  unifyTermsWH wh t r
unifyTermsWH wh (VectT lt ln) (VectT rt rn) = do
  s1 <- unifyTermsWH wh lt rt
  s2 <- unifyTermsWH wh ln rn
  return $ s1 <> s2
unifyTermsWH wh (FinT l) (FinT r) = do
  unifyTermsWH wh l r
unifyTermsWH wh (EqT l1 l2) (EqT r1 r2) = do
  s1 <- unifyTermsWH wh l1 r1
  s2 <- unifyTermsWH wh l2 r2
  return $ s1 <> s2
unifyTermsWH wh (LteT l1 l2) (LteT r1 r2) = do
  s1 <- unifyTermsWH wh l1 r1
  s2 <- unifyTermsWH wh l2 r2
  return $ s1 <> s2
unifyTermsWH _ FZ FZ = return noSub
unifyTermsWH wh (FS l) (FS r) = do
  unifyTermsWH wh l r
unifyTermsWH _ Z Z = return noSub
unifyTermsWH wh (S l) (S r) = do
  unifyTermsWH wh l r
unifyTermsWH _ LNil LNil = return noSub
unifyTermsWH wh (LCons l1 l2) (LCons r1 r2) = do
  s1 <- unifyTermsWH wh l1 r1
  s2 <- unifyTermsWH wh l2 r2
  return $ s1 <> s2
unifyTermsWH _ VNil VNil = return noSub
unifyTermsWH wh (VCons l1 l2) (VCons r1 r2) = do
  s1 <- unifyTermsWH wh l1 r1
  s2 <- unifyTermsWH wh l2 r2
  return $ s1 <> s2
unifyTermsWH wh (MJust l) (MJust r) = do
  unifyTermsWH wh l r
unifyTermsWH _ MNothing MNothing = return noSub
unifyTermsWH wh (Refl l) (Refl r) = do
  unifyTermsWH wh l r
unifyTermsWH _ LTEZero LTEZero = return noSub
unifyTermsWH wh (LTESucc l) (LTESucc r) = do
  unifyTermsWH wh l r
unifyTermsWH wh (App l1 l2) (App r1 r2) =
  do
    s1 <- unifyTermsWH wh l1 r1
    s2 <- unifyTermsWH wh l2 r2
    return $ s1 <> s2
    `catchError` (\_ -> normaliseAndUnifyTerms wh (App l1 l2) (App r1 r2))
unifyTermsWH wh l r = normaliseAndUnifyTerms wh l r

-- | Unify two terms.
unifyTerms :: Term -> Term -> Tc Sub
unifyTerms = unifyTermsWH []

-- | Unify two terms and return the substituted left term
unifyToLeft :: Term -> Term -> Tc Term
unifyToLeft l r = do
  s <- unifyTerms l r
  return $ sub s l

-- | Unify two terms, normalising them first.
normaliseAndUnifyTerms :: [Var] -> Term -> Term -> Tc Sub
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

-- | Convert a pattern to a term
patToTerm :: Pat -> Tc Term
patToTerm (VP v) = return (V v)
patToTerm WildP = V <$> freshVar
patToTerm ZP = return Z
patToTerm (SP p) = S <$> patToTerm p
patToTerm FZP = return FZ
patToTerm (FSP p) = FS <$> patToTerm p
patToTerm LNilP = return LNil
patToTerm (LConsP p1 p2) = LCons <$> patToTerm p1 <*> patToTerm p2
patToTerm VNilP = return VNil
patToTerm (VConsP p1 p2) = VCons <$> patToTerm p1 <*> patToTerm p2
patToTerm (MJustP p) = MJust <$> patToTerm p
patToTerm MNothingP = return MNothing
patToTerm (ReflP p) = Refl <$> patToTerm p
patToTerm LTEZeroP = return LTEZero
patToTerm (LTESuccP p) = LTESucc <$> patToTerm p
patToTerm (PairP p1 p2) = Pair <$> patToTerm p1 <*> patToTerm p2
patToTerm (CtorP i args) = foldM (\t p -> App t <$> patToTerm p) (Global i) args
