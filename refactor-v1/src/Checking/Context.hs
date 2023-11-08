module Checking.Context
  ( Judgement (..),
    Ctx (..),
    GlobalCtx (..),
    TcState (..),
    Tc,
    TcError (..),
    emptyTcState,
    inGlobalCtx,
    inCtx,
    enterCtxMod,
    addTyping,
    addDecl,
    withinCtx,
    lookupTypeOrError,
    lookupDecl,
    lookupType,
    freshHole,
    freshVar,
    modifyCtx,
    enterCtx,
    modifyGlobalCtx,
  )
where

import Control.Monad.Except (throwError)
import Control.Monad.State (MonadState (..), StateT)
import Data.List (intercalate)
import Lang (Clause, Decl (..), Pat, Term (..), Type, Var (..))

-- | A typing judgement.
data Judgement = Typing Var Type

instance Show Judgement where
  show (Typing v ty) = show v ++ " : " ++ show ty

-- | A context, represented as a list of typing judgements.
newtype Ctx = Ctx [Judgement]

instance Show Ctx where
  show (Ctx js) = intercalate "\n" $ map show js

-- | The global context, represented as a list of string-decl pairs.
newtype GlobalCtx = GlobalCtx [(String, Decl)]

-- | A typechecking error.
data TcError
  = VariableNotFound Var
  | Mismatch Term Term
  | DeclNotFound String
  | CannotUnifyTwoHoles Var Var
  | CannotInferHoleType Var
  | NeedMoreTypeHints [Var]
  | TooManyPatterns Clause Pat
  | TooFewPatterns Clause Type

instance Show TcError where
  show (VariableNotFound v) = "Variable not found: " ++ show v
  show (Mismatch t1 t2) = "Term mismatch: " ++ show t1 ++ " vs " ++ show t2
  show (DeclNotFound s) = "Declaration not found: " ++ s
  show (CannotUnifyTwoHoles h1 h2) = "Cannot unify two holes: " ++ show h1 ++ " and " ++ show h2
  show (CannotInferHoleType h) = "Cannot infer hole type: " ++ show h
  show (NeedMoreTypeHints vs) = "Need more type hints to resolve the holes: " ++ show vs
  show (TooManyPatterns c p) = "Too many patterns in '" ++ show c ++ "' . Unexpected: " ++ show p
  show (TooFewPatterns c t) = "Too few patterns in '" ++ show c ++ "'. Expected pattern for: " ++ show t

-- | The typechecking state.
data TcState = TcState
  { -- | The current context.
    ctx :: Ctx,
    -- | The global context.
    globalCtx :: GlobalCtx,
    -- | Unique variable counter.
    varCounter :: Int
  }

-- | The empty typechecking state.
emptyTcState :: TcState
emptyTcState = TcState (Ctx []) (GlobalCtx []) 0

-- | The typechecking monad.
type Tc a = StateT TcState (Either TcError) a

-- | Map over some context.
withSomeCtx :: (TcState -> c) -> (c -> Tc a) -> Tc a
withSomeCtx ct f = do
  s <- get
  f (ct s)

-- | Monadic map over the current context.
withinCtx :: (Ctx -> Tc a) -> Tc a
withinCtx = withSomeCtx ctx

-- | Map over the current context.
inCtx :: (Ctx -> a) -> Tc a
inCtx f = withSomeCtx ctx (return . f)

-- | Map over the global context.
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

-- | Enter a new context and exit it after the operation.
enterCtx :: Tc a -> Tc a
enterCtx = enterCtxMod id

-- | Update the current context.
modifyCtx :: (Ctx -> Ctx) -> Tc ()
modifyCtx f = do
  s <- get
  put $ s {ctx = f (ctx s)}

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
  Nothing -> throwError $ VariableNotFound v
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

-- | Get a fresh variable.
freshVar :: Tc Var
freshVar = do
  s <- get
  let h = varCounter s
  put $ s {varCounter = h + 1}
  return $ Var ("h" ++ show h) h

-- | Get a fresh hole.
freshHole :: Tc Term
freshHole = do
  v <- freshVar
  return $ Hole v
