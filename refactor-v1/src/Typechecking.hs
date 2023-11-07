module Typechecking (unifyTerms, checkTerm, inferTerm, emptyTcState, unifyToLeft, normaliseTermFully, TcState (..)) where

import Control.Applicative (Alternative ((<|>)))
import Control.Monad.Except (MonadError (catchError))
import Control.Monad.State.Lazy (MonadState (..), MonadTrans (lift), StateT)
import Data.List (intercalate, intersperse)
import Debug.Trace (trace)
import GHC.IO.Handle.Text (memcpy)
import Lang (Decl (..), Pat (..), Term (..), Type, Var (..))
import Vars (Sub (..), Subst (sub), alphaRename, noSub, subVar, var)

data Judgement = Typing Var Type

instance Show Judgement where
  show (Typing v ty) = show v ++ " : " ++ show ty

-- | A context, represented as a list of variable-type pairs.
newtype Ctx = Ctx [Judgement]

instance Show Ctx where
  show (Ctx js) = intercalate "\n" $ map show js

-- | The global context, represented as a list of string-decl pairs.
newtype GlobalCtx = GlobalCtx [(String, Decl)]

-- | A typechecking error.
data TcError = VariableNotFound Var | Mismatch Term Term | DeclNotFound String | CannotUnifyTwoHoles Var Var | CannotInferHoleType Var

instance Show TcError where
  show (VariableNotFound v) = "Variable not found: " ++ show v
  show (Mismatch t1 t2) = "Term mismatch: " ++ show t1 ++ " vs " ++ show t2
  show (DeclNotFound s) = "Declaration not found: " ++ s
  show (CannotUnifyTwoHoles h1 h2) = "Cannot unify two holes: " ++ show h1 ++ " and " ++ show h2
  show (CannotInferHoleType h) = "Cannot infer hole type: " ++ show h

-- | The typechecking state.
data TcState = TcState
  { -- | The current context.
    ctx :: Ctx,
    -- | The global context.
    globalCtx :: GlobalCtx,
    -- | Hole counter.
    holeCounter :: Int
  }

-- | The empty typechecking state.
emptyTcState :: TcState
emptyTcState = TcState (Ctx []) (GlobalCtx []) 0

-- | The typechecking monad.
type Tc a = StateT TcState (Either TcError) a

-- | Map over the current context.
withSomeCtx :: (TcState -> c) -> (c -> Tc a) -> Tc a
withSomeCtx ct f = do
  s <- get
  f (ct s)

withinCtx :: (Ctx -> Tc a) -> Tc a
withinCtx = withSomeCtx ctx

inCtx :: (Ctx -> a) -> Tc a
inCtx f = withSomeCtx ctx (return . f)

inGlobalCtx :: (GlobalCtx -> a) -> Tc a
inGlobalCtx f = withSomeCtx globalCtx (return . f)

-- | Update the current context.
enterCtxMod :: (Ctx -> Ctx) -> Tc a -> Tc a -- todo: substitute in a
enterCtxMod f op = do
  s <- get
  let prevCtx = ctx s
  put $ s {ctx = f prevCtx}
  res <- op
  put $ s {ctx = prevCtx}
  return res

-- | Update the global context.
modifyGlobalCtx :: (GlobalCtx -> GlobalCtx) -> Tc ()
modifyGlobalCtx f = do
  s <- get
  put $ s {globalCtx = f (globalCtx s)}

-- | Lookup the type of a variable in the current context.
lookupType :: Var -> Ctx -> Maybe Type
lookupType _ (Ctx []) = Nothing
lookupType v (Ctx ((Typing v' ty) : c)) = if v == v' then Just ty else lookupType v (Ctx c)

-- | Lookup the type of a variable in the current context.
lookupTypeOrError :: Var -> Ctx -> Tc Type
lookupTypeOrError v c = case lookupType v c of
  Nothing -> tcErr $ VariableNotFound v
  Just ty -> return ty

-- | Lookup the declaration of a global variable in the global context.
lookupDecl :: String -> GlobalCtx -> Maybe Decl
lookupDecl _ (GlobalCtx []) = Nothing
lookupDecl s (GlobalCtx ((s', d) : c)) = if s == s' then Just d else lookupDecl s (GlobalCtx c)

-- | Add a variable to the current context.
addTyping :: Var -> Type -> Ctx -> Ctx
addTyping v t (Ctx c) = Ctx (Typing v t : c)

-- | Add a declaration to the global context.
addDecl :: Decl -> GlobalCtx -> GlobalCtx
addDecl d (GlobalCtx c) = GlobalCtx ((declName d, d) : c)

-- | Signal a type error.
tcErr :: TcError -> Tc a
tcErr e = lift (Left e)

-- | Get a fresh hole.
freshHole :: Tc Term
freshHole = do
  s <- get
  let h = holeCounter s
  put $ s {holeCounter = h + 1}
  let holeVar = Var ("h" ++ show h) h
  return $ Hole holeVar

-- | Infer the type of a term.
inferTerm :: Term -> Tc Type
inferTerm (PiT v t1 t2) = do
  s <- checkTerm t1 TyT
  _ <- enterCtxMod (addTyping v (sub s t1)) $ inferTerm (sub s t2)
  return TyT
inferTerm (SigmaT v t1 t2) = do
  s <- checkTerm t1 TyT
  _ <- enterCtxMod (addTyping v (sub s t1)) $ inferTerm (sub s t2)
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
  ty1 <- inferTerm t1
  ty2 <- inferTerm t2
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
  varTy <- inferTerm t2
  let v = var "x"
  let inferredTy = PiT v varTy bodyTy
  s <- checkTerm t1 inferredTy
  return $ subVar v (sub s t2) (sub s bodyTy)
inferTerm (Hole h) = tcErr $ CannotInferHoleType h
inferTerm (Global g) = do
  decl <- inGlobalCtx (lookupDecl g)
  case decl of
    Nothing -> tcErr $ DeclNotFound g
    Just decl' -> return $ declTy decl'
inferTerm (Refl t) = return $ EqT t t
inferTerm Z = return NatT
inferTerm (S n) = do
  nTy <- inferTerm n
  _ <- unifyTerms nTy NatT
  return NatT
inferTerm LNil = do
  ty <- freshHole
  return $ ListT ty
inferTerm (LCons h t) = do
  ty <- inferTerm h
  ty' <- inferTerm t
  unifyToLeft (ListT ty) ty'
inferTerm (MJust t) = do
  ty <- inferTerm t
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

-- | Check the type of a term
checkTerm :: Term -> Type -> Tc Sub
checkTerm (Lam v t) (PiT var' ty1 ty2) = do
  enterCtxMod (addTyping v ty1) $ checkTerm t (alphaRename var' v ty2)
checkTerm (Pair t1 t2) (SigmaT v ty1 ty2) = do
  s1 <- checkTerm t1 ty1
  s2 <- checkTerm (sub s1 t2) (subVar v (sub s1 t1) (sub s1 ty2))
  return $ s1 <> s2
checkTerm term (Hole h) = do
  inferred <- inferTerm term
  return $ Sub [(h, inferred)]
checkTerm term ty = do
  inferred <- inferTerm term
  unifyTerms inferred ty

normaliseTerm :: Term -> Tc (Maybe Term)
normaliseTerm (App (Lam v t1) t2) = do
  return . Just $ subVar v t2 t1
normaliseTerm (App t1 t2) = do
  t1' <- normaliseTerm t1
  case t1' of
    Nothing -> return Nothing
    Just t1'' -> do
      return . Just $ App t1'' t2
normaliseTerm _ = return Nothing -- TODO

normaliseTermFully :: Term -> Tc Term
normaliseTermFully t = do
  t' <- normaliseTerm t
  case t' of
    Nothing -> return t
    Just t'' -> normaliseTermFully t''

-- | Unify two terms.
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
    else tcErr $ Mismatch (V l) (V r)
unifyTerms (Global l) (Global r) =
  if l == r
    then return noSub
    else normaliseAndUnifyTerms (Global l) (Global r)
unifyTerms (Hole l) (Hole r) =
  if l == r
    then return noSub
    else tcErr $ CannotUnifyTwoHoles l r
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
        Nothing -> tcErr $ Mismatch l r
        Just r'' -> unifyTerms l r''
    Just l'' -> do
      unifyTerms l'' r
