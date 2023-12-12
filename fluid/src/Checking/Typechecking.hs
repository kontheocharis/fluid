module Checking.Typechecking
  ( checkTerm,
    unifyTerms,
    inferTerm,
    normaliseTermFully,
    checkProgram,
    runUntilFixpoint,
    substituteHolesIn,
  )
where

import Checking.Context
  ( NextProblem (..),
    Problem (problemCtx),
    Tc,
    TcError (..),
    TcState (..),
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
    resolveHole,
    resolveSub,
  )
import Checking.Vars (Sub (..), Subst (sub), alphaRename, noSub, subInM, subSize, subVar)
import Control.Arrow (first)
import Control.Monad (foldM, foldM_, mapAndUnzipM, replicateM)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.State (modify)
import Data.Bifunctor (second)
import Data.Maybe (fromJust)
import Debug.Trace (trace, traceShow)
import Lang
  ( Clause (..),
    CtorItem (..),
    DataItem (..),
    DeclItem (..),
    Item (..),
    Pat (..),
    PiMode (..),
    Program (..),
    Term (..),
    TermMappable,
    Type,
    Var,
    listToPiType,
    piTypeToList,
    prependPatToClause,
  )
import Parsing.Resolution (termToPat)

-- | Substitute all holes in a term from the context.
substituteHolesIn :: (Eq a, TermMappable a) => a -> Tc a
substituteHolesIn t = do
  s <- inState resolvedHoles
  t' <- subInM s t
  if t == t'
    then return t
    else substituteHolesIn t'

-- | Run the typechecker on a job until there are no more problems.
runUntilFixpoint :: (Eq a, TermMappable a) => Tc a -> Tc a
runUntilFixpoint job = do
  c <- inState holeCounter
  runUntilFixpoint' c
  where
    runUntilFixpoint' c = do
      modify $ \s -> s {holeCounter = c}
      res <- job
      p <- remainingProblems
      if p == 0
        then substituteHolesIn res
        else do
          n <- remainingHoles
          (_, seenProblems) <- runNextProblems 0 []
          n' <- remainingHoles
          if n' < n
            then
              if n' == 0
                then substituteHolesIn res
                else runUntilFixpoint' c
            else throwError $ CannotSolveProblems seenProblems
    runNextProblems :: Int -> [Problem] -> Tc (Int, [Problem])
    runNextProblems nSubbed seenProblems = do
      result <- inNextProblem unifyTermsWH
      case result of
        NoNextProblem -> return (nSubbed, seenProblems)
        Success p s -> do
          resolveSub s
          runNextProblems (nSubbed + subSize s) (p : seenProblems)

-- | Check the program
checkProgram :: Program -> Tc Program
checkProgram (Program decls) = do
  mapM_ checkItem decls
  return $ Program decls

-- | Check some item in the program.
checkItem :: Item -> Tc ()
checkItem (Decl decl) = checkDeclItem decl
checkItem (Data dat) = checkDataItem dat

-- | Check a data item.
checkDataItem :: DataItem -> Tc ()
checkDataItem dItem@(DataItem name ty ctors) = do
  -- Check the signature of the data type.
  checkTerm ty TyT
  let (tys, ret) = piTypeToList ty
  unifyTerms ret TyT
  let ty' = listToPiType (tys, ret)

  -- Then, add the declaration to the context.
  enterGlobalCtxMod (addItem (Data (DataItem name ty' ctors))) $ do
    -- Then, check each constructor.
    mapM_ (checkCtorItem ty') ctors

  -- Now add the final data type to the context.
  modifyGlobalCtx (addItem (Data dItem))

checkCtorItem :: Type -> CtorItem -> Tc ()
checkCtorItem dTy (CtorItem _ ty dTyName) = do
  -- The amount of arguments of the data type
  let dTyArgModes = map (\(m, _, _) -> m) $ fst $ piTypeToList dTy

  -- Check the signature of the constructor.
  checkTerm ty TyT
  let (tys, ret) = piTypeToList ty

  -- \| Add all the arguments to the context
  enterCtxMod (\c -> foldr (\(_, v, t) c' -> addTyping v t False c') c tys) $ do
    -- \| Check that the return type is the data type.
    dummyArgs <-
      mapM
        ( \m -> do
            h <- freshHole
            return (m, h)
        )
        dTyArgModes
    let dummyRet = foldl (\r (m, h) -> App m r h) (Global dTyName) dummyArgs
    unifyTerms ret dummyRet

-- | Check a declaration.
-- This is self-contained, so it does not produce a substitution.
checkDeclItem :: DeclItem -> Tc ()
checkDeclItem decl = do
  -- Check the type of the declaration.
  let ty = declTy decl
  checkTerm ty TyT
  let tys = piTypeToList ty

  -- The, add the declaration to the context.
  enterGlobalCtxMod (addItem (Decl decl)) $ do
    -- Then, check each clause.
    mapM_ (enterCtx . checkClause tys) (declClauses decl)

  -- Substitute back into the type
  modifyGlobalCtx (addItem (Decl decl))

-- | Check a clause against a list of types which are its signature.
checkClause :: ([(PiMode, Var, Type)], Type) -> Clause -> Tc ()
checkClause ([], t) (Clause [] r) = do
  checkTerm r t
checkClause ((tm, v, a) : as, t) (Clause ((cm, p) : ps) r) = do
  -- TODO: Check tm = cm
  (pt, _) <- patToTerm p -- TODO: substitute back vars
  enterPat $ checkTerm pt a
  let s = Sub [(v, pt)]
  checkClause (map (second (sub s)) as, sub s t) (Clause ps r)
checkClause ([], _) cl@(Clause ((m, p) : _) _) = throwError $ TooManyPatterns cl p
checkClause ((_, _, t) : _, _) cl@(Clause [] _) = throwError $ TooFewPatterns cl t
checkClause _ (ImpossibleClause _) = error "Impossible clauses not yet supported"

-- | Check the type of a term. (The type itself should already be checked.)
-- This might produce a substitution.
checkTerm :: Term -> Type -> Tc ()
checkTerm Wild _ = return ()
checkTerm (Lam lm v t) (PiT pm var' ty1 ty2) | lm == pm = do
  enterCtxMod (addTyping v ty1 False) $ checkTerm t (alphaRename var' v ty2)
checkTerm (Lam lm v t) typ = do
  varTy <- freshHole
  bodyTy <- enterCtxMod (addTyping v varTy False) $ inferTerm t
  let inferredTy = PiT lm v varTy bodyTy
  _ <- unifyTerms typ inferredTy
  checkTerm (Lam lm v t) inferredTy
checkTerm (Pair t1 t2) (SigmaT v ty1 ty2) = do
  _ <- checkTerm t1 ty1
  resolvedTy2 <- substituteHolesIn ty2
  checkTerm t2 (subVar v t1 resolvedTy2)
checkTerm (Pair t1 t2) typ = do
  fstTy <- freshHole
  sndTy <- freshHole
  v <- freshVar
  let inferredTy = SigmaT v fstTy sndTy
  _ <- checkTerm (Pair t1 t2) inferredTy
  unifyTerms typ inferredTy
checkTerm (PiT _ v t1 t2) typ = do
  checkTerm t1 TyT
  _ <- enterCtxMod (addTyping v t1 False) $ inferTerm t2
  unifyTerms typ TyT
checkTerm (SigmaT v t1 t2) typ = do
  checkTerm t1 TyT
  _ <- enterCtxMod (addTyping v t1 False) $ inferTerm t2
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
        else throwError $ VariableNotFound v
    Just vTyp' -> case typ of
      Hole h -> resolveHole h vTyp'
      _ -> unifyTerms typ vTyp'
checkTerm (App m t1 t2) typ = do
  piTy <- inferTerm t1
  case piTy of
    PiT Implicit _ _ _ | m == Explicit -> do
      h <- freshHole
      let newTerm = App Explicit (App Implicit t1 h) t2
      checkTerm newTerm typ
    PiT m' v varTy bodyTy | m == m' -> do
      checkTerm t2 varTy
      resolvedBodyTy <- substituteHolesIn bodyTy
      unifyTerms typ $ subVar v t2 resolvedBodyTy
    _ -> do
      var <- freshVar
      varTy <- freshHole
      bodyTy <- freshHole
      let inferredTy = PiT m var varTy bodyTy
      unifyTerms piTy inferredTy
checkTerm (Hole h) ty = do
  hTerm <- lookupHole h
  case hTerm of
    Nothing -> do
      hTy <- freshHoleVar
      resolveHole hTy ty
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
checkCtor :: [Var] -> [Type] -> Type -> [Term] -> Type -> Tc ()
checkCtor implicitVars ctorParams ctorRet ctorArgs annotType = do
  let implicitVarHoles = map Hole implicitVars
  let implicitVarSub = Sub $ zip implicitVars implicitVarHoles
  let instantiatedCtorRet = sub implicitVarSub ctorRet
  retSub <- unifyTermsWH implicitVars annotType instantiatedCtorRet
  foldM_
    ( \ss (ty, arg) -> do
        checkTerm arg (sub ss ty)
        return ss
    )
    (implicitVarSub <> retSub)
    (zip ctorParams ctorArgs)

-- | Infer the type of a term.
inferTerm :: Term -> Tc Type
inferTerm t = do
  ty <- freshHole
  _ <- checkTerm t ty
  substituteHolesIn ty

-- | Reduce a term to normal form (one step).
-- If this is not possible, return Nothing.
normaliseTerm :: Term -> Tc (Maybe Term)
normaliseTerm (App am (Lam lm v t1) t2) | am == lm = do
  return . Just $ subVar v t2 t1
normaliseTerm (App m t1 t2) = do
  t1' <- normaliseTerm t1
  case t1' of
    Nothing -> return Nothing
    Just t1'' -> do
      return . Just $ App m t1'' t2
normaliseTerm _ = return Nothing -- TODO: normalise declarations

-- | Reduce a term to normal form (fully).
normaliseTermFully :: Term -> Tc Term
normaliseTermFully t = do
  t' <- normaliseTerm t
  case t' of
    Nothing -> return t
    Just t'' -> normaliseTermFully t''

-- | Unify two terms.
unifyTermsWH :: [Var] -> Term -> Term -> Tc Sub
unifyTermsWH wh l r = do
  s1 <- unifyTermsWH' wh l r
  resolveSub s1
  return s1

-- | Unify two terms.
-- This might produce a substitution.
-- Unification is currently symmetric.
--
-- This also accepts a list of "weak holes" to always unify with the other side,
-- even if the other side is a hole.
unifyTermsWH' :: [Var] -> Term -> Term -> Tc Sub
unifyTermsWH' wh (PiT lm lv l1 l2) (PiT rm rv r1 r2) | lm == rm = do
  s1 <- unifyTermsWH' wh l1 r1
  s2 <- unifyTermsWH' wh l2 (alphaRename rv lv r2)
  return (s1 <> s2)
unifyTermsWH' wh (SigmaT lv l1 l2) (SigmaT rv r1 r2) = do
  s1 <- unifyTermsWH' wh l1 r1
  s2 <- unifyTermsWH' wh l2 (alphaRename rv lv r2)
  return $ s1 <> s2
unifyTermsWH' wh (Lam lm lv l) (Lam rm rv r) | lm == rm = do
  unifyTermsWH' wh l (alphaRename rv lv r)
unifyTermsWH' wh (Pair l1 l2) (Pair r1 r2) = do
  s1 <- unifyTermsWH' wh l1 r1
  s2 <- unifyTermsWH' wh l2 r2
  return $ s1 <> s2
unifyTermsWH' _ TyT TyT = return noSub
unifyTermsWH' wh (Hole l) (Hole r)
  | l == r = return noSub
  -- Check for weak holes before refusing to unify.
  | l `elem` wh = return $ Sub [(l, Hole r)]
  | r `elem` wh = return $ Sub [(r, Hole l)]
  | otherwise = do
      lTerm <- lookupHole l
      case lTerm of
        Nothing -> do
          rTerm <- lookupHole r
          case rTerm of
            Nothing -> do
              pushProblem wh (Hole l) (Hole r)
              return noSub
            Just r' -> unifyTermsWH' wh (Hole l) r'
        Just l' -> unifyTermsWH' wh l' (Hole r)
unifyTermsWH' wh (Hole h) t = do
  hTerm <- lookupHole h
  case hTerm of
    Nothing -> do
      return $ Sub [(h, t)]
    Just t' -> unifyTermsWH' wh t' t
unifyTermsWH' wh t (Hole h) = do
  hTerm <- lookupHole h
  case hTerm of
    Nothing -> do
      return $ Sub [(h, t)]
    Just t' -> unifyTermsWH' wh t t'
unifyTermsWH' _ (V l) (V r) | l == r = return noSub
unifyTermsWH' _ (V v) t = do
  -- Pattern bindings can always be unified with.
  patBind <- inCtx (isPatBind v)
  p <- inState inPat
  if patBind == Just True && p
    then do
      return $ Sub [(v, t)]
    else throwError $ Mismatch (V v) t
unifyTermsWH' _ t (V v) = do
  -- Pattern bindings can always be unified with.
  patBind <- inCtx (isPatBind v)
  p <- inState inPat
  if patBind == Just True && p
    then do
      return $ Sub [(v, t)]
    else do
      throwError $ Mismatch (V v) t
unifyTermsWH' wh (Global l) (Global r) =
  if l == r
    then return noSub
    else normaliseAndUnifyTerms wh (Global l) (Global r)
unifyTermsWH' _ NatT NatT = return noSub
unifyTermsWH' wh (ListT t) (ListT r) = do
  unifyTermsWH' wh t r
unifyTermsWH' wh (MaybeT t) (MaybeT r) = do
  unifyTermsWH' wh t r
unifyTermsWH' wh (VectT lt ln) (VectT rt rn) = do
  s1 <- unifyTermsWH' wh lt rt
  s2 <- unifyTermsWH' wh ln rn
  return $ s1 <> s2
unifyTermsWH' wh (FinT l) (FinT r) = do
  unifyTermsWH' wh l r
unifyTermsWH' wh (EqT l1 l2) (EqT r1 r2) = do
  s1 <- unifyTermsWH' wh l1 r1
  s2 <- unifyTermsWH' wh l2 r2
  return $ s1 <> s2
unifyTermsWH' wh (LteT l1 l2) (LteT r1 r2) = do
  s1 <- unifyTermsWH' wh l1 r1
  s2 <- unifyTermsWH' wh l2 r2
  return $ s1 <> s2
unifyTermsWH' _ FZ FZ = return noSub
unifyTermsWH' wh (FS l) (FS r) = do
  unifyTermsWH' wh l r
unifyTermsWH' _ Z Z = return noSub
unifyTermsWH' wh (S l) (S r) = do
  unifyTermsWH' wh l r
unifyTermsWH' _ LNil LNil = return noSub
unifyTermsWH' wh (LCons l1 l2) (LCons r1 r2) = do
  s1 <- unifyTermsWH' wh l1 r1
  s2 <- unifyTermsWH' wh l2 r2
  return $ s1 <> s2
unifyTermsWH' _ VNil VNil = return noSub
unifyTermsWH' wh (VCons l1 l2) (VCons r1 r2) = do
  s1 <- unifyTermsWH' wh l1 r1
  s2 <- unifyTermsWH' wh l2 r2
  return $ s1 <> s2
unifyTermsWH' wh (MJust l) (MJust r) = do
  unifyTermsWH' wh l r
unifyTermsWH' _ MNothing MNothing = return noSub
unifyTermsWH' wh (Refl l) (Refl r) = do
  unifyTermsWH' wh l r
unifyTermsWH' _ LTEZero LTEZero = return noSub
unifyTermsWH' wh (LTESucc l) (LTESucc r) = do
  unifyTermsWH' wh l r
unifyTermsWH' wh (App lm l1 l2) (App rm r1 r2)
  | lm == rm =
      do
        s1 <- unifyTermsWH' wh l1 r1
        s2 <- unifyTermsWH' wh l2 r2
        return $ s1 <> s2
        `catchError` (\_ -> normaliseAndUnifyTerms wh (App lm l1 l2) (App rm r1 r2))
unifyTermsWH' wh (App lm l1 l2) (App rm r1 r2) = normaliseAndUnifyTerms wh (App lm l1 l2) (App rm r1 r2)
unifyTermsWH' wh l r = normaliseAndUnifyTerms wh l r

-- | Unify two terms.
unifyTerms :: Term -> Term -> Tc ()
unifyTerms a b = do
  _ <- unifyTermsWH [] a b
  return ()

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
patToTerm :: Pat -> Tc (Term, [Var])
patToTerm WildP = do
  v <- freshVar
  return (V v, [v])
patToTerm (VP v) = return (V v, [])
patToTerm (SP p) = do
  (t, vs) <- patToTerm p
  return (S t, vs)
patToTerm (FSP p) = do
  (t, vs) <- patToTerm p
  return (FS t, vs)
patToTerm ZP = return (Z, [])
patToTerm FZP = return (FZ, [])
patToTerm LNilP = return (LNil, [])
patToTerm VNilP = return (VNil, [])
patToTerm (LConsP p1 p2) = do
  (t1, vs1) <- patToTerm p1
  (t2, vs2) <- patToTerm p2
  return (LCons t1 t2, vs1 ++ vs2)
patToTerm (VConsP p1 p2) = do
  (t1, vs1) <- patToTerm p1
  (t2, vs2) <- patToTerm p2
  return (VCons t1 t2, vs1 ++ vs2)
patToTerm (MJustP p) = do
  (t, vs) <- patToTerm p
  return (MJust t, vs)
patToTerm MNothingP = return (MNothing, [])
patToTerm (ReflP p) = do
  (t, vs) <- patToTerm p
  return (Refl t, vs)
patToTerm LTEZeroP = return (LTEZero, [])
patToTerm (LTESuccP p) = do
  (t, vs) <- patToTerm p
  return (LTESucc t, vs)
patToTerm (PairP p1 p2) = do
  (t1, vs1) <- patToTerm p1
  (t2, vs2) <- patToTerm p2
  return (Pair t1 t2, vs1 ++ vs2)
patToTerm (CtorP i args) = do
  (args', vss) <- mapAndUnzipM patToTerm args
  return (foldl (App Explicit) (Global i) args', concat vss)
