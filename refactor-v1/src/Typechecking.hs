module Typechecking () where

import Control.Monad.State.Lazy (MonadState (..), MonadTrans (lift), StateT)
import Lang (Decl (..), Pat (..), Term (..), Type, Var (..))
import Vars (alphaRename, subVar)

data Judgement = Typing Var Type | Equality Var Term Type

-- | A context, represented as a list of variable-type pairs.
newtype Ctx = Ctx [Judgement]

-- | The global context, represented as a list of string-decl pairs.
newtype GlobalCtx = GlobalCtx [(String, Decl)]

-- | A typechecking error.
data TcError = VariableNotFound Var | Mismatch Term Term

instance Show TcError where
  show (VariableNotFound v) = "Variable not found: " ++ show v
  show (Mismatch t1 t2) = "Term mismatch: " ++ show t1 ++ " vs " ++ show t2

-- | The typechecking state.
data TcState = TcState
  { -- | The current context.
    ctx :: Ctx,
    -- | The global context.
    globalCtx :: GlobalCtx,
    -- | Hole counter.
    holeCounter :: Int
  }

-- | The typechecking monad.
type Tc a = StateT TcState (Either TcError) a

-- | Map over the current context.
withSomeCtx :: (TcState -> c) -> (c -> a) -> Tc a
withSomeCtx ct f = do
  s <- get
  return $ f (ct s)

inCtx :: (Ctx -> a) -> Tc a
inCtx = withSomeCtx ctx

inGlobalCtx :: (GlobalCtx -> a) -> Tc a
inGlobalCtx = withSomeCtx globalCtx

-- | Update the current context.
enterCtxMod :: (Ctx -> Ctx) -> Tc a -> Tc a
enterCtxMod f op = do
  s <- get
  let prevCtx = ctx s
  put $ s {ctx = f prevCtx}
  res <- op
  put $ s {ctx = prevCtx}
  return res

modifyCtx :: (Ctx -> Ctx) -> Tc ()
modifyCtx f = do
  s <- get
  put $ s {ctx = f (ctx s)}

-- | Update the current context.
enterGlobalCtxMod :: (GlobalCtx -> GlobalCtx) -> Tc a -> Tc a
enterGlobalCtxMod f op = do
  s <- get
  let prevCtx = globalCtx s
  put $ s {globalCtx = f prevCtx}
  res <- op
  put $ s {globalCtx = prevCtx}
  return res

modifyGlobalCtx :: (GlobalCtx -> GlobalCtx) -> Tc ()
modifyGlobalCtx f = do
  s <- get
  put $ s {globalCtx = f (globalCtx s)}

-- | Get the current context.
getCtx :: Tc Ctx
getCtx = inCtx id

-- | Get the current global context.
getGlobalCtx :: Tc GlobalCtx
getGlobalCtx = inGlobalCtx id

-- | Lookup the type of a variable in the current context.
lookupType :: Var -> Ctx -> Maybe Type
lookupType _ (Ctx []) = Nothing
lookupType v (Ctx ((Typing v' ty) : c)) = if v == v' then Just ty else lookupType v (Ctx c)
lookupType v (Ctx ((Equality v' _ ty) : c)) = if v == v' then Just ty else lookupType v (Ctx c)

-- | Lookup the type of a variable in the current context.
lookupValue :: Var -> Ctx -> Maybe Term
lookupValue _ (Ctx []) = Nothing
lookupValue v (Ctx ((Typing v' _) : c)) = if v == v' then Just (V v) else lookupValue v (Ctx c)
lookupValue v (Ctx ((Equality v' t _) : c)) = if v == v' then Just t else lookupValue v (Ctx c)

-- | Lookup the declaration of a global variable in the global context.
lookupDecl :: String -> GlobalCtx -> Maybe Decl
lookupDecl _ (GlobalCtx []) = Nothing
lookupDecl s (GlobalCtx ((s', d) : c)) = if s == s' then Just d else lookupDecl s (GlobalCtx c)

-- | Add a variable to the current context.
addTyping :: Var -> Type -> Ctx -> Ctx
addTyping v t (Ctx c) = Ctx (Typing v t : c)

-- | Add an equality to the current context.
addEq :: Var -> Term -> Type -> Ctx -> Ctx
addEq v t ty (Ctx c) = Ctx (Equality v t ty : c)

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
  return $ Hole (Var ("h" ++ show h) h)

-- | Check the type of a term
checkTerm :: Term -> Type -> Tc (Term, Type)
checkTerm (V var) ty = do
  varTy <- inCtx (lookupType var)
  case varTy of
    Nothing -> tcErr $ VariableNotFound var
    Just varTy' -> do
      actualTy <- unifyTerms varTy' ty
      return (V var, actualTy)
checkTerm (Lam var t) (PiT var' ty1 ty2) = do
  (t', ty2') <- enterCtxMod (addTyping var ty1) $ checkTerm t (alphaRename var' var ty2) -- ensure to substitute variables back
  return (Lam var t', PiT var' ty1 (alphaRename var var' ty2'))
checkTerm (Pair t1 t2) (SigmaT v ty1 ty2) = do
  (t1', ty1') <- checkTerm t1 ty1
  (t2', ty2') <- enterCtxMod (addEq v t1' ty1') $ checkTerm t2 ty2
  return (Pair t1' t2', SigmaT v ty1' (alphaRename v v ty2'))

-- | Infer the type of a term.
inferTerm :: Term -> Tc Type
inferTerm t = do
  h <- freshHole
  (_, ty) <- checkTerm t h
  return ty

-- | Unify two terms.
unifyTerms :: Term -> Term -> Tc Term
unifyTerms (PiT lv l1 l2) (PiT rv r1 r2) = do
  l1' <- unifyTerms l1 r1
  l2' <- unifyTerms l2 (alphaRename rv lv r2)
  return $ PiT lv l1' l2'
unifyTerms (SigmaT lv l1 l2) (SigmaT rv r1 r2) = do
  l1' <- unifyTerms l1 r1
  l2' <- unifyTerms l2 (alphaRename rv lv r2)
  return $ SigmaT lv l1' l2'
unifyTerms (Lam lv l) (Lam rv r) = do
  l' <- unifyTerms l (alphaRename rv lv r)
  return $ Lam lv l'
unifyTerms (Pair l1 l2) (Pair r1 r2) = do
  l1' <- unifyTerms l1 r1
  l2' <- unifyTerms l2 r2
  return $ Pair l1' l2'
unifyTerms TyT TyT = return TyT
unifyTerms (V l) (V r) =
  if l == r
    then return $ V l
    else tcErr $ Mismatch (V l) (V r) -- TODO: check in context
unifyTerms (Global l) (Global r) =
  if l == r
    then return $ Global l
    else tcErr $ Mismatch (Global l) (Global r)
unifyTerms (Hole l) (Hole r) =
  if l == r
    then return $ Hole l
    else tcErr $ Mismatch (Hole l) (Hole r) -- TODO: check in context
unifyTerms NatT NatT = return NatT
unifyTerms (ListT t) (ListT r) = do
  t' <- unifyTerms t r
  return $ ListT t'
unifyTerms (MaybeT t) (MaybeT r) = do
  t' <- unifyTerms t r
  return $ MaybeT t'
unifyTerms (VectT lt ln) (VectT rt rn) = do
  lt' <- unifyTerms lt rt
  ln' <- unifyTerms ln rn
  return $ VectT lt' ln'
unifyTerms (FinT l) (FinT r) = do
  l' <- unifyTerms l r
  return $ FinT l'
unifyTerms (EqT l1 l2) (EqT r1 r2) = do
  l1' <- unifyTerms l1 r1
  l2' <- unifyTerms l2 r2
  return $ EqT l1' l2'
unifyTerms (LteT l1 l2) (LteT r1 r2) = do
  l1' <- unifyTerms l1 r1
  l2' <- unifyTerms l2 r2
  return $ LteT l1' l2'
unifyTerms FZ FZ = return FZ
unifyTerms (FS l) (FS r) = do
  l' <- unifyTerms l r
  return $ FS l'
unifyTerms Z Z = return Z
unifyTerms (S l) (S r) = do
  l' <- unifyTerms l r
  return $ S l'
unifyTerms LNil LNil = return LNil
unifyTerms (LCons l1 l2) (LCons r1 r2) = do
  l1' <- unifyTerms l1 r1
  l2' <- unifyTerms l2 r2
  return $ LCons l1' l2'
unifyTerms VNil VNil = return VNil
unifyTerms (VCons l1 l2) (VCons r1 r2) = do
  l1' <- unifyTerms l1 r1
  l2' <- unifyTerms l2 r2
  return $ VCons l1' l2'
unifyTerms (MJust l) (MJust r) = do
  l' <- unifyTerms l r
  return $ MJust l'
unifyTerms MNothing MNothing = return MNothing
unifyTerms (Refl l) (Refl r) = do
  l' <- unifyTerms l r
  return $ Refl l'
unifyTerms LTEZero LTEZero = return LTEZero
unifyTerms (LTESucc l) (LTESucc r) = do
  l' <- unifyTerms l r
  return $ LTESucc l'
unifyTerms (Hole h) t = do
  ty <- inferTerm t
  modifyCtx (addEq h t ty)
  return t
unifyTerms t (Hole h) = do
  ty <- inferTerm t
  modifyCtx (addEq h t ty)
  return t
unifyTerms (App l1 l2) (App r1 r2) = error "TODO"
unifyTerms l (App r1 r2) = error "TODO"
unifyTerms (App l1 l2) r = error "TODO"
unifyTerms l r = tcErr $ Mismatch l r
