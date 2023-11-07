module Typechecking () where

import Control.Applicative (Alternative ((<|>)))
import Control.Monad.Except (MonadError (catchError))
import Control.Monad.State.Lazy (MonadState (..), MonadTrans (lift), StateT)
import GHC.IO.Handle.Text (memcpy)
import Lang (Decl (..), Pat (..), Term (..), Type, Var (..))
import Vars (Sub (..), Subst (sub), alphaRename, noSub, subVar)

data Judgement = Typing Var Type

-- | A context, represented as a list of variable-type pairs.
newtype Ctx = Ctx [Judgement]

-- | The global context, represented as a list of string-decl pairs.
newtype GlobalCtx = GlobalCtx [(String, Decl)]

-- | A typechecking error.
data TcError = VariableNotFound Var | Mismatch Term Term | DeclNotFound String | CannotUnifyTwoHoles Var Var | CannotCheckHoleType Var Type

instance Show TcError where
  show (VariableNotFound v) = "Variable not found: " ++ show v
  show (Mismatch t1 t2) = "Term mismatch: " ++ show t1 ++ " vs " ++ show t2
  show (DeclNotFound s) = "Declaration not found: " ++ s
  show (CannotUnifyTwoHoles h1 h2) = "Cannot unify two holes: " ++ show h1 ++ " and " ++ show h2
  show (CannotCheckHoleType h ty) = "Cannot check hole type: " ++ show h ++ " : " ++ show ty

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

enterCtx :: Tc a -> Tc a
enterCtx = enterCtxMod id

modifyCtx :: (Ctx -> Ctx) -> Tc ()
modifyCtx f = do
  s <- get
  put $ s {ctx = f (ctx s)}

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
inferTerm t = do
  h <- freshHole
  s <- checkTerm t h
  return (sub s h)

-- | Check the type of a term
checkTerm :: Term -> Type -> Tc Sub
checkTerm (V var) ty = do
  varTy <- withinCtx (lookupTypeOrError var)
  unifyTerms ty varTy
checkTerm (Lam var t) (PiT var' ty1 ty2) = do
  enterCtxMod (addTyping var ty1) $ checkTerm t (alphaRename var' var ty2)
checkTerm (Pair t1 t2) (SigmaT v ty1 ty2) = do
  s1 <- checkTerm t1 ty1
  s2 <- checkTerm (sub s1 t2) (subVar v (sub s1 t1) (sub s1 ty2))
  return $ s1 <> s2
checkTerm (App t1 t2) ty = do
  ty1 <- inferTerm t1
  case ty1 of
    PiT v ty1v ty1b -> do
      s1 <- checkTerm t2 ty1v
      s2 <- checkTerm (sub s1 ty) (subVar v (sub s1 t2) (sub s1 ty1b))
      return $ s1 <> s2
    _ -> tcErr $ Mismatch t1 ty
checkTerm (Hole h) ty = tcErr $ CannotCheckHoleType h ty
checkTerm (Global g) ty = do
  decl <- inGlobalCtx (lookupDecl g)
  case decl of
    Nothing -> tcErr $ DeclNotFound g
    Just decl' -> do
      unifyTerms ty (declTy decl')
checkTerm (Refl t) (EqT t1 t2) = do
  s1 <- unifyTerms t t1
  s2 <- unifyTerms (sub s1 t) (sub s1 t2)
  return $ s1 <> s2
checkTerm (FS t) (FinT n) = error "TODO"
checkTerm (S t) NatT = checkTerm t NatT
checkTerm Z NatT = return noSub
checkTerm LNil (ListT ty) = return noSub
checkTerm (LCons t1 t2) (ListT ty) = do
  s1 <- checkTerm t1 ty
  s2 <- checkTerm t2 (ListT (sub s1 ty))
  return $ s1 <> s2
checkTerm (VCons t1 t2) (VectT ty n) = error "TODO"
checkTerm (MJust t) (MaybeT ty) = checkTerm t ty
checkTerm MNothing (MaybeT _) = return noSub
checkTerm (LTESucc t) (LteT ty1 ty2) = error "TODO"
checkTerm FZ (FinT (S n)) = error "TODO"
checkTerm VNil (VectT ty n) = error "TODO"
checkTerm term ty = do
  normed <- normaliseTerm ty
  case normed of
    Nothing -> do
      normedTerm <- normaliseTerm term
      case normedTerm of
        Nothing -> tcErr $ Mismatch term ty
        Just normedTerm' -> do
          checkTerm normedTerm' ty
    Just ty' -> do
      checkTerm term ty'

normaliseTerm :: Term -> Tc (Maybe Term)
normaliseTerm (V _) = return Nothing
normaliseTerm (Lam _ _) = return Nothing
-- normaliseTerm (App t1 t2) = do
--   t1' <- normaliseTerm t1
--   case t1' of
--     Nothing -> do
--       t2' <- normaliseTerm t2
--       case t2' of
--         Nothing -> return Nothing
--         Just t2'' -> return $ Just $ App t1 t2''
--     Just t1'' -> do
--       t2' <- normaliseTerm t2
--       case t2' of
--         Nothing -> return $ Just $ App t1'' t2
--         Just t2'' -> return $ Just $ App t1'' t2''
normaliseTerm _ = return Nothing -- TODO

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
