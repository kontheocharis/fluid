module Checking.Context
  ( Judgement (..),
    Ctx (..),
    GlobalCtx (..),
    TcState (..),
    Tc,
    TcError (..),
    FlexApp (..),
    emptyTcState,
    inGlobalCtx,
    inCtx,
    enterCtxMod,
    enterGlobalCtxMod,
    inState,
    addTyping,
    addSubst,
    addItem,
    withinCtx,
    lookupTypeOrError,
    lookupItemOrCtor,
    enterPat,
    lookupType,
    lookupSubst,
    freshVar,
    modifyCtx,
    enterCtx,
    modifyGlobalCtx,
    runTc,
    setType,
    solveMeta,
    freshMeta,
    freshMetaAt,
    classifyApp,
    registerHole,
    registerWild,
  )
where

import Control.Applicative ((<|>))
import Control.Monad.Except (throwError)
import Control.Monad.State (MonadState (..), StateT (runStateT))
import Data.List (find, intercalate)
import Data.Map (Map, empty, insert)
import Interface.Pretty
import Lang
  ( Clause,
    CtorItem (..),
    DataItem (DataItem),
    HasLoc (..),
    Item (..),
    Loc (..),
    Pat,
    Term (..),
    TermValue (..),
    Type,
    Var (..),
    genTerm,
    itemName,
    listToApp,
    locatedAt,
  )

-- | A typing judgement.
data Judgement = Typing Var Type | Subst Var Term

instance Show Judgement where
  show (Typing v ty) = printVal v ++ " : " ++ printVal ty
  show (Subst v t) = printVal v ++ " = " ++ printVal t

-- | A context, represented as a list of typing judgements.
newtype Ctx = Ctx [Judgement]

instance Show Ctx where
  show (Ctx js) = intercalate "\n" $ map show js

-- | The global context, represented as a list of string-decl pairs.
newtype GlobalCtx = GlobalCtx [Item] deriving (Show)

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
  | NotAFunction Term
  | CaseIsNotImpossible Clause

instance Show TcError where
  show (VariableNotFound v) = "Variable not found: " ++ printVal v
  show (Mismatch t1 t2) = "Term mismatch: " ++ printVal t1 ++ " vs " ++ printVal t2
  show (ItemNotFound s) = "Item not found: " ++ s
  show (CannotUnifyTwoHoles h1 h2) = "Cannot unify two holes: " ++ show h1 ++ " and " ++ show h2
  show (CannotInferHoleType h) = "Cannot infer hole type: " ++ show h
  show (NeedMoreTypeHints vs) = "Need more type hints to resolve the holes: " ++ show vs
  show (TooManyPatterns c p) = "Too many patterns in '" ++ show c ++ "' . Unexpected: " ++ show p
  show (TooFewPatterns c t) = "Too few patterns in '" ++ show c ++ "'. Expected pattern for: " ++ show t
  show (NotAFunction t) = "Not a function: " ++ show t
  show (CaseIsNotImpossible c) = "Case is not impossible: " ++ show c

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
    -- | Meta values, indexed by variable.
    metaValues :: Map Var Term,
    -- | Hole/wild locations, to substitute in the end.
    holeLocs :: Map Loc (Maybe Var)
  }
  deriving (Show)

-- | The empty typechecking state.
emptyTcState :: TcState
emptyTcState = TcState (Ctx []) (GlobalCtx []) 0 False empty empty empty

-- | The typechecking monad.
type Tc a = StateT TcState (Either TcError) a

-- | Run a typechecking computation.
runTc :: Tc a -> Either TcError (a, TcState)
runTc tc = do
  (res, endState) <- runStateT tc emptyTcState
  return (res, endState)

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

-- | Lookup a substitution of a variable in the current context.
lookupSubst :: Var -> Ctx -> Maybe Term
lookupSubst _ (Ctx []) = Nothing
lookupSubst v (Ctx ((Subst v' term) : c)) = if v == v' then Just term else lookupSubst v (Ctx c)
lookupSubst v (Ctx (_ : c)) = lookupSubst v (Ctx c)

-- | Lookup the type of a variable in the current context.
lookupType :: Var -> Ctx -> Maybe Type
lookupType _ (Ctx []) = Nothing
lookupType v (Ctx ((Typing v' ty) : c)) = if v == v' then Just ty else lookupType v (Ctx c)
lookupType v (Ctx (_ : c)) = lookupType v (Ctx c)

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
addTyping :: Var -> Type -> Ctx -> Ctx
addTyping v t (Ctx c) = Ctx (Typing v t : c)

-- | Add a substitution to the current context.
addSubst :: Var -> Term -> Ctx -> Ctx
addSubst v t (Ctx c) = Ctx (Subst v t : c)

-- | Add a declaration to the global context.
addItem :: Item -> GlobalCtx -> GlobalCtx
addItem d (GlobalCtx c) = GlobalCtx (d : c)

-- | Get a fresh variable.
freshVarPrefixed :: String -> Tc Var
freshVarPrefixed n = do
  s <- get
  let h = varCounter s
  put $ s {varCounter = h + 1}
  return $ Var (n ++ show h) h

-- | Get a fresh variable.
freshVar :: Tc Var
freshVar = freshVarPrefixed "v"

-- | Get all variables in a context.
ctxVars :: Ctx -> [Var]
ctxVars (Ctx []) = []
ctxVars (Ctx ((Typing v _) : c)) = v : ctxVars (Ctx c)
ctxVars (Ctx (_ : c)) = ctxVars (Ctx c)

-- | Get a fresh applied metavariable in the current context.
freshMetaAt :: (HasLoc a) => a -> Tc Term
freshMetaAt h = do
  v <- freshVarPrefixed "m"
  vrs <- inCtx ctxVars
  let (m, ms) = (genTerm (Meta v), map (genTerm . V) vrs)
  let t = listToApp (m, ms)
  return $ locatedAt h (termValue t)

-- | Get a fresh applied metavariable in the current context.
freshMeta :: Tc Term
freshMeta = freshMetaAt NoLoc

-- | Register a hole.
registerHole :: Loc -> Var -> Tc ()
registerHole l v = do
  s <- get
  put $ s {holeLocs = insert l (Just v) (holeLocs s)}

-- | Register an underscore/wild.
registerWild :: Loc -> Tc ()
registerWild l = do
  s <- get
  put $ s {holeLocs = insert l Nothing (holeLocs s)}

-- | Solve a meta.
solveMeta :: Var -> Term -> Tc ()
solveMeta h t = do
  s <- get
  put $ s {metaValues = insert h t (metaValues s)}

-- | A flexible (meta) application.
data FlexApp = Flex Var [Term] deriving (Show)

-- | Add a term to a `FlexApp`
addTerm :: Term -> FlexApp -> FlexApp
addTerm t (Flex h ts) = Flex h (ts ++ [t])

-- | Interpret a `FlexApp`
classifyApp :: Term -> Maybe FlexApp
classifyApp (Term (Meta h) _) = return $ Flex h []
classifyApp (Term (App t1 t2) _) = do
  c <- classifyApp t1
  return $ addTerm t2 c
classifyApp _ = Nothing
