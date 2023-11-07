module Typechecking (unifyTerms, checkTerm, inferTerm, unifyToLeft, normaliseTermFully, checkProgram) where

import Context
  ( Tc,
    TcError (..),
    addDecl,
    addTyping,
    enterCtx,
    enterCtxMod,
    freshHole,
    freshHoleVar,
    inCtx,
    inGlobalCtx,
    lookupDecl,
    lookupTypeOrError,
    modifyCtx,
    modifyGlobalCtx,
    withinCtx,
  )
import Control.Monad.Except (catchError, throwError)
import Data.Bifunctor (second)
import Debug.Trace (trace)
import Lang (Clause (..), Decl (..), Pat (..), Program (..), Term (..), Type, Var, patToTerm, piTypeToList)
import Vars (Sub (..), Subst (sub), alphaRename, noSub, subVar, var)

-- | Check the program
checkProgram :: Program -> Tc ()
checkProgram (Program decls) = mapM_ checkDecl decls

-- | Check a declaration.
-- This is self-contained, so it does not produce a substitution.
checkDecl :: Decl -> Tc ()
checkDecl decl = do
  -- First, check the type of the declaration.
  checkTermSelfContained (declTy decl) TyT
  let tys = piTypeToList (declTy decl)
  -- The, add the declaration to the context.
  modifyGlobalCtx (addDecl decl)
  -- Then, check each clause.
  mapM_ (\c -> enterCtx $ checkClause tys c) (declClauses decl)

-- | Check a clause against a list of types which are its signature.
checkClause :: ([(Var, Type)], Type) -> Clause -> Tc ()
checkClause ([], t) (Clause [] r) = do
  c <- inCtx id
  trace (show ("___", c)) $ checkTermSelfContained r t
checkClause ((v, a) : as, t) (Clause (p : ps) r) = do
  s <- checkPat p a
  let s' = s <> Sub [(v, sub s (patToTerm p))]
  checkClause (map (second (sub s')) as, sub s' t) (Clause ps r)
checkClause ([], _) cl@(Clause (p : _) _) = throwError $ TooManyPatterns cl p
checkClause ((_, t) : _, _) cl@(Clause [] _) = throwError $ TooFewPatterns cl t
checkClause _ (ImpossibleClause _) = error "Impossible clauses not yet supported"

-- | Check the type of a term. (The type itself should already be checked.)
-- This might produce a substitution.
checkTerm :: Term -> Type -> Tc Sub
checkTerm (Lam v t) (PiT var' ty1 ty2) = do
  enterCtxMod (addTyping v ty1) $ checkTerm t (alphaRename var' v ty2)
checkTerm (Pair t1 t2) (SigmaT v ty1 ty2) = do
  s1 <- checkTerm t1 ty1
  s2 <- checkTerm (sub s1 t2) (subVar v (sub s1 t1) (sub s1 ty2))
  return $ s1 <> s2
checkTerm (Wild Nothing) _ = return noSub -- TODO: need to do this recursively in infer somehow
checkTerm (Wild (Just v)) ty = do
  -- Add the wildcard to the context.
  modifyCtx (addTyping v ty)
  return noSub
checkTerm term (Hole h) = do
  inferred <- inferTerm term
  return $ Sub [(h, inferred)]
checkTerm term ty = do
  inferred <- inferTerm term
  unifyTerms inferred ty

-- | Check the type of a term, without producing a substitution.
checkTermSelfContained :: Term -> Type -> Tc ()
checkTermSelfContained term ty = do
  _ <- checkTerm term ty
  return ()

-- | Check a pattern against a type.
checkPat :: Pat -> Type -> Tc Sub
checkPat p = checkTerm (patToTerm p)

-- | Infer the type of a term through `checkTerm` with a hole.
-- Meant to be used from within `inferTerm`.
inferByCheck :: Term -> Tc Type
inferByCheck t = do
  ty <- freshHole
  s <- checkTerm t ty
  return $ sub s ty

-- | Infer the type of a term. TODO: merge this with `checkTerm`
inferTerm :: Term -> Tc Type
inferTerm (PiT v t1 t2) = do
  s <- checkTerm t1 TyT
  _ <- enterCtxMod (addTyping v (sub s t1)) $ inferByCheck (sub s t2)
  return TyT
inferTerm (SigmaT v t1 t2) = do
  s <- checkTerm t1 TyT
  _ <- enterCtxMod (addTyping v (sub s t1)) $ inferByCheck (sub s t2)
  return TyT
inferTerm TyT = return TyT
inferTerm NatT = return TyT
inferTerm (ListT t) = do
  _ <- checkTerm t TyT
  return TyT
inferTerm (VectT t n) = do
  _ <- checkTerm t TyT
  _ <- checkTerm n NatT
  return TyT
inferTerm (FinT t) = do
  _ <- checkTerm t NatT
  return TyT
inferTerm (EqT t1 t2) = do
  ty1 <- inferByCheck t1
  ty2 <- inferByCheck t2
  _ <- unifyTerms ty1 ty2
  return TyT
inferTerm (LteT t1 t2) = do
  _ <- checkTerm t1 NatT
  _ <- checkTerm t2 NatT
  return TyT
inferTerm (MaybeT t) = do
  _ <- checkTerm t TyT
  return TyT
inferTerm (V v) = do
  withinCtx (lookupTypeOrError v)
inferTerm (Wild _) = do
  v <- freshHoleVar
  return $ Hole v
inferTerm (Lam v t) = do
  bodyTy <- freshHole
  varTy <- freshHole
  let inferredTy = PiT v varTy bodyTy
  s <- checkTerm (Lam v t) inferredTy
  return $ sub s inferredTy
inferTerm (Pair t1 t2) = do
  fstTy <- freshHole
  sndTy <- freshHole
  let inferredTy = SigmaT (var "x") fstTy sndTy
  s <- checkTerm (Pair t1 t2) inferredTy
  return $ sub s inferredTy
inferTerm (App t1 t2) = do
  bodyTy <- freshHole
  varTy <- inferByCheck t2
  let v = var "x"
  let inferredTy = PiT v varTy bodyTy
  s <- checkTerm t1 inferredTy
  return $ subVar v (sub s t2) (sub s bodyTy)
inferTerm (Hole h) = throwError $ CannotInferHoleType h
inferTerm (Global g) = do
  decl <- inGlobalCtx (lookupDecl g)
  case decl of
    Nothing -> throwError $ DeclNotFound g
    Just decl' -> return $ declTy decl'
inferTerm (Refl t) = return $ EqT t t
inferTerm Z = return NatT
inferTerm (S n) = do
  nTy <- inferByCheck n
  _ <- unifyTerms nTy NatT
  return NatT
inferTerm LNil = do
  ty <- freshHole
  return $ ListT ty
inferTerm (LCons h t) = do
  ty <- inferByCheck h
  ty' <- inferByCheck t
  unifyToLeft (ListT ty) ty'
inferTerm (MJust t) = do
  ty <- inferByCheck t
  return $ MaybeT ty
inferTerm MNothing = do
  ty <- freshHole
  return $ MaybeT ty
inferTerm LTEZero = error "TODO"
inferTerm (LTESucc t) = error "TODO"
inferTerm FZ = error "TODO"
inferTerm (FS t) = error "TODO"
inferTerm VNil = error "TODO"
inferTerm (VCons t1 t2) = error "TODO"

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

-- | Unify two terms.
-- This might produce a substitution.
-- Unification is currently symmetric.
unifyTerms :: Term -> Term -> Tc Sub
unifyTerms (PiT lv l1 l2) (PiT rv r1 r2) = do
  s1 <- unifyTerms l1 r1
  s2 <- unifyTerms l2 (alphaRename rv lv r2)
  return $ s1 <> s2
unifyTerms (SigmaT lv l1 l2) (SigmaT rv r1 r2) = do
  s1 <- unifyTerms l1 r1
  s2 <- unifyTerms l2 (alphaRename rv lv r2)
  return $ s1 <> s2
unifyTerms (Lam lv l) (Lam rv r) = do
  unifyTerms l (alphaRename rv lv r)
unifyTerms (Pair l1 l2) (Pair r1 r2) = do
  s1 <- unifyTerms l1 r1
  s2 <- unifyTerms l2 r2
  return $ s1 <> s2
unifyTerms TyT TyT = return noSub
unifyTerms (V l) (V r) =
  if l == r
    then return noSub
    else throwError $ Mismatch (V l) (V r)
unifyTerms (Global l) (Global r) =
  if l == r
    then return noSub
    else normaliseAndUnifyTerms (Global l) (Global r)
unifyTerms (Hole l) (Hole r) =
  if l == r
    then return noSub
    else throwError $ CannotUnifyTwoHoles l r
unifyTerms NatT NatT = return noSub
unifyTerms (ListT t) (ListT r) = do
  unifyTerms t r
unifyTerms (MaybeT t) (MaybeT r) = do
  unifyTerms t r
unifyTerms (VectT lt ln) (VectT rt rn) = do
  s1 <- unifyTerms lt rt
  s2 <- unifyTerms ln rn
  return $ s1 <> s2
unifyTerms (FinT l) (FinT r) = do
  unifyTerms l r
unifyTerms (EqT l1 l2) (EqT r1 r2) = do
  s1 <- unifyTerms l1 r1
  s2 <- unifyTerms l2 r2
  return $ s1 <> s2
unifyTerms (LteT l1 l2) (LteT r1 r2) = do
  s1 <- unifyTerms l1 r1
  s2 <- unifyTerms l2 r2
  return $ s1 <> s2
unifyTerms FZ FZ = return noSub
unifyTerms (FS l) (FS r) = do
  unifyTerms l r
unifyTerms Z Z = return noSub
unifyTerms (S l) (S r) = do
  unifyTerms l r
unifyTerms LNil LNil = return noSub
unifyTerms (LCons l1 l2) (LCons r1 r2) = do
  s1 <- unifyTerms l1 r1
  s2 <- unifyTerms l2 r2
  return $ s1 <> s2
unifyTerms VNil VNil = return noSub
unifyTerms (VCons l1 l2) (VCons r1 r2) = do
  s1 <- unifyTerms l1 r1
  s2 <- unifyTerms l2 r2
  return $ s1 <> s2
unifyTerms (MJust l) (MJust r) = do
  unifyTerms l r
unifyTerms MNothing MNothing = return noSub
unifyTerms (Refl l) (Refl r) = do
  unifyTerms l r
unifyTerms LTEZero LTEZero = return noSub
unifyTerms (LTESucc l) (LTESucc r) = do
  unifyTerms l r
unifyTerms (Hole h) t = do
  return $ Sub [(h, t)]
unifyTerms t (Hole h) = do
  return $ Sub [(h, t)]
unifyTerms (App l1 l2) (App r1 r2) =
  do
    s1 <- unifyTerms l1 r1
    s2 <- unifyTerms l2 r2
    return $ s1 <> s2
    `catchError` (\_ -> normaliseAndUnifyTerms (App l1 l2) (App r1 r2))
unifyTerms l r = normaliseAndUnifyTerms l r

-- | Unify two terms, and ensure that the substitution is empty.
unifyTermsSelfContained :: Term -> Term -> Tc ()
unifyTermsSelfContained l r = do
  _ <- unifyTerms l r
  return ()

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
