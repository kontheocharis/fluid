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
    enterGlobalCtxMod,
    inState,
    addTyping,
    addItem,
    withinCtx,
    lookupTypeOrError,
    lookupItemOrCtor,
    isPatBind,
    enterPat,
    lookupType,
    freshHole,
    freshHoleVar,
    freshVar,
    modifyCtx,
    enterCtx,
    modifyGlobalCtx,
    runTc,
    setType,
    solveHole,
    resolveShallow,
  )
where

import Control.Applicative ((<|>))
import Control.Monad.Except (throwError)
import Control.Monad.State (MonadState (..), StateT (runStateT))
import Data.List (find, intercalate)
import Data.Map (Map, empty, insert, (!?))
import Debug.Trace (trace)
import Lang
  ( Clause,
    CtorItem (..),
    DataItem (DataItem),
    HasLoc (..),
    Item (..),
    Loc,
    Pat,
    Term (..),
    TermValue (..),
    Type,
    Var (..),
    genTerm,
    itemName,
  )

-- | A typing judgement.
data Judgement = Typing
  { judgementVar :: Var,
    judgementType :: Type,
    -- Whether this is a pattern binding.
    judgementIsPatBind :: Bool
  }

instance Show Judgement where
  show (Typing v ty b) = show v ++ " : " ++ show ty ++ (if b then " (pat)" else "")

-- | A context, represented as a list of typing judgements.
newtype Ctx = Ctx [Judgement]

instance Show Ctx where
  show (Ctx js) = intercalate "\n" $ map show js

-- | The global context, represented as a list of string-decl pairs.
newtype GlobalCtx = GlobalCtx [Item]

-- | A typechecking error.
data TcError
  = VariableNotFound Var
  | Mismatch Term Term
  | ItemNotFound String
  | CannotUnifyTwoHoles Var Var
  | CannotInferHoleType Var
  | NeedMoreTypeHints [Var]
  | TooManyPatterns Clause Pat
  | TooFewPatterns Clause Type

instance Show TcError where
  show (VariableNotFound v) = "Variable not found: " ++ show v
  show (Mismatch t1 t2) = "Term mismatch: " ++ show t1 ++ " vs " ++ show t2
  show (ItemNotFound s) = "Item not found: " ++ s
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
    varCounter :: Int,
    -- | Whether we are in a pattern
    inPat :: Bool,
    -- | Term types, indexed by location.
    termTypes :: Map Loc Type,
    -- | Holes
    holeValues :: Map Var Term
  }

-- | The empty typechecking state.
emptyTcState :: TcState
emptyTcState = TcState (Ctx []) (GlobalCtx []) 0 False empty empty

-- | The typechecking monad.
type Tc a = StateT TcState (Either TcError) a

-- | Run a typechecking computation.
runTc :: Tc a -> Either TcError a
runTc tc = do
  (res, _) <- runStateT tc emptyTcState
  return res

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

-- | Map over the current typechecking state.
inState :: (TcState -> a) -> Tc a
inState f = withSomeCtx id (return . f)

-- | Map over the global context.
inGlobalCtx :: (GlobalCtx -> a) -> Tc a
inGlobalCtx f = withSomeCtx globalCtx (return . f)

-- | Set the type of a term.
setType :: Term -> Type -> Tc ()
setType t ty = do
  s <- get
  case termTypes s !? getLoc t of
    Just ty' -> trace ("Found existing type for " ++ show t ++ " : " ++ show ty ++ ", which is " ++ show ty') $ return ()
    Nothing -> return ()
  put $ s {termTypes = insert (getLoc t) ty (termTypes s)}

-- | Enter a pattern by setting the inPat flag to True.
enterPat :: Tc a -> Tc a
enterPat p = do
  s <- get
  put $ s {inPat = True}
  res <- p
  s' <- get
  put $ s' {inPat = False}
  return res

-- | Update the current context.
enterCtxMod :: (Ctx -> Ctx) -> Tc a -> Tc a -- todo: substitute in a
enterCtxMod f op = do
  s <- get
  let prevCtx = ctx s
  put $ s {ctx = f prevCtx}
  res <- op
  s' <- get
  put $ s' {ctx = prevCtx}
  return res

-- | Update the current global context.
enterGlobalCtxMod :: (GlobalCtx -> GlobalCtx) -> Tc a -> Tc a -- todo: substitute in a
enterGlobalCtxMod f op = do
  s <- get
  let prevCtx = globalCtx s
  put $ s {globalCtx = f prevCtx}
  res <- op
  s' <- get
  put $ s' {globalCtx = prevCtx}
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
lookupType v (Ctx ((Typing v' ty _) : c)) = if v == v' then Just ty else lookupType v (Ctx c)

-- | Lookup the type of a variable in the current context.
isPatBind :: Var -> Ctx -> Maybe Bool
isPatBind _ (Ctx []) = Nothing
isPatBind v (Ctx ((Typing v' _ b) : _)) | v' == v = Just b
isPatBind v (Ctx ((Typing {}) : c)) = isPatBind v (Ctx c)

-- | Lookup the type of a variable in the current context.
lookupTypeOrError :: Var -> Ctx -> Tc Type
lookupTypeOrError v c = case lookupType v c of
  Nothing -> throwError $ VariableNotFound v
  Just ty -> return ty

-- | Lookup the declaration of a global variable in the global context.
lookupItemOrCtor :: String -> GlobalCtx -> Maybe (Either Item CtorItem)
lookupItemOrCtor _ (GlobalCtx []) = Nothing
lookupItemOrCtor s (GlobalCtx (d : _)) | s == itemName d = Just (Left d)
lookupItemOrCtor s (GlobalCtx ((Data (DataItem _ _ ctors)) : c)) =
  (Right <$> find (\(CtorItem name _ _) -> name == s) ctors) <|> lookupItemOrCtor s (GlobalCtx c)
lookupItemOrCtor s (GlobalCtx (_ : c)) = lookupItemOrCtor s (GlobalCtx c)

-- | Add a variable to the current context.
addTyping :: Var -> Type -> Bool -> Ctx -> Ctx
addTyping v t b (Ctx c) = Ctx (Typing v t b : c)

-- | Add a declaration to the global context.
addItem :: Item -> GlobalCtx -> GlobalCtx
addItem d (GlobalCtx c) = GlobalCtx (d : c)

-- | Get a fresh variable.
freshVar :: Tc Var
freshVar = do
  s <- get
  let h = varCounter s
  put $ s {varCounter = h + 1}
  return $ Var ("v" ++ show h) h

-- | Get a fresh variable.
freshHoleVar :: Tc Var
freshHoleVar = do
  s <- get
  let h = varCounter s
  put $ s {varCounter = h + 1}
  return $ Var ("h" ++ show h) h

-- | Get a fresh hole.
freshHole :: Tc Term
freshHole = genTerm . Hole <$> freshHoleVar

-- | Solve a hole.
solveHole :: Var -> Term -> Tc ()
solveHole h t = do
  s <- get
  put $ s {holeValues = insert h t (holeValues s)}

-- | Resolve a term by filling in holes if present.
resolveShallow :: Term -> Tc Term
resolveShallow (Term (Hole h) d) = do
  s <- get
  case holeValues s !? h of
    Just t -> resolveShallow t
    Nothing -> return $ Term (Hole h) d
resolveShallow (Term (App t1 t2) d) = do
  t1' <- resolveShallow t1
  return $ Term (App t1' t2) d
resolveShallow t = return t
