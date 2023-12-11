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
    inNextProblem,
    pushProblem,
    resolveHole,
    resolveSub,
    deferProblem,
    remainingHoles,
    remainingProblems,
    NextProblem (..),
    Problem (..),
  )
where

import Checking.Vars (Sub (..))
import Control.Applicative ((<|>))
import Control.Monad.Error.Class (tryError)
import Control.Monad.Except (MonadError (catchError), throwError)
import Control.Monad.State (MonadState (..), StateT (runStateT))
import Data.List (find, intercalate)
import Data.Map (Map, empty, insert)
import Lang
  ( Clause,
    CtorItem (..),
    DataItem (DataItem),
    Item (..),
    Pat,
    Term (..),
    Type,
    Var (..),
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
  | CannotSolveProblems [Problem]
  | CannotInferHoleType Var
  | NeedMoreTypeHints [Var]
  | TooManyPatterns Clause Pat
  | TooFewPatterns Clause Type

instance Show TcError where
  show (VariableNotFound v) = "Variable not found: " ++ show v
  show (Mismatch t1 t2) = "Term mismatch: " ++ show t1 ++ " vs " ++ show t2
  show (ItemNotFound s) = "Item not found: " ++ s
  show (CannotUnifyTwoHoles h1 h2) = "Cannot unify two holes: " ++ show h1 ++ " and " ++ show h2
  show (CannotSolveProblems ps) = "Cannot unify:" ++ intercalate "\n" (map (\p -> "\t" ++ show (problemSrc p) ++ " with " ++ show (problemTarget p)) ps)
  show (CannotInferHoleType h) = "Cannot infer hole type: " ++ show h
  show (NeedMoreTypeHints vs) = "Need more type hints to resolve the holes: " ++ show vs
  show (TooManyPatterns c p) = "Too many patterns in '" ++ show c ++ "' . Unexpected: " ++ show p
  show (TooFewPatterns c t) = "Too few patterns in '" ++ show c ++ "'. Expected pattern for: " ++ show t

-- | A unification problem.
data Problem = Problem
  { -- The context to enter when solving the problem.
    problemCtx :: Ctx,
    -- Whether we are in a pattern.
    problemInPat :: Bool,
    -- The variables that are implicit.
    problemImplicitVars :: [Var], -- TODO: delete
    -- Source term to unify.
    problemSrc :: Term,
    -- Target term to unify.
    problemTarget :: Term
  }

-- | The typechecking state.
data TcState = TcState
  { -- | The current context.
    ctx :: Ctx,
    -- | The global context.
    globalCtx :: GlobalCtx,
    -- | Unique hole counter.
    holeCounter :: Int,
    -- | Unique variable counter.
    varCounter :: Int,
    -- | Whether we are in a pattern
    inPat :: Bool,
    -- | Partial map from holes to terms
    resolvedHoles :: Map Var Term,
    -- | Unification problems
    problems :: [Problem]
  }

-- \| Unification problems

-- | The empty typechecking state.
emptyTcState :: TcState
emptyTcState = TcState (Ctx []) (GlobalCtx []) 0 0 False empty []

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

-- | Enter a pattern by setting the inPat flag to True.
enterPat :: Tc a -> Tc a
enterPat p = do
  s <- get
  put $ s {inPat = True}
  res <- p
  s' <- get
  put $ s' {inPat = False}
  return res

-- | Set the inPat flag to the given `b`.
enterPatMod :: Bool -> Tc a -> Tc a
enterPatMod b p = do
  s <- get
  let prevB = inPat s
  put $ s {inPat = b}
  res <- p
  s' <- get
  put $ s' {inPat = prevB}
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
  let h = holeCounter s
  put $ s {holeCounter = h + 1}
  return $ Var ("h" ++ show h) h

-- | Get a fresh hole.
freshHole :: Tc Term
freshHole = Hole <$> freshHoleVar

-- | Result of running a computation on a unification problem.
data NextProblem a = NoNextProblem | Success Problem a | Failure Problem TcError

-- | Progress to the next unification problem and run the given computation.
--
-- If the computation returns Nothing, the problem is "not solved".
inNextProblem :: ([Var] -> Term -> Term -> Tc a) -> Tc (NextProblem a)
inNextProblem f = do
  s <- get
  case problems s of
    [] -> return NoNextProblem
    (p@(Problem pCtx pInPat pImplicitVars pSrc pTarget) : ps) -> do
      res <- enterPatMod pInPat . enterCtxMod (const pCtx) $ tryError (f pImplicitVars pSrc pTarget)
      case res of
        Right r -> do
          put $ s {problems = ps}
          return $ Success p r
        Left e -> do
          put $ s {problems = ps}
          return $ Failure p e

-- | Add a unification problem.
pushProblem :: [Var] -> Term -> Term -> Tc ()
pushProblem vs t1 t2 = do
  s <- get
  put $ s {problems = problems s ++ [Problem (ctx s) (inPat s) vs t1 t2]}

-- | Defer the current unification problem.
deferProblem :: Tc ()
deferProblem = do
  s <- get
  case problems s of
    [] -> return ()
    (p : ps) -> put $ s {problems = ps ++ [p]}

-- | Resolve a hole to a term.
resolveHole :: Var -> Term -> Tc ()
resolveHole h t = do
  s <- get
  put $ s {resolvedHoles = insert h t (resolvedHoles s)}

-- | Resolve a substitution.
resolveSub :: Sub -> Tc ()
resolveSub (Sub ((v, t) : xs)) = do
  resolveHole v t
  resolveSub (Sub xs)
resolveSub (Sub []) = return ()

-- | Get the amount of remaining holes.
remainingHoles :: Tc Int
remainingHoles = do
  s <- get
  return $ length (problems s) - length (resolvedHoles s)

-- | Get the amount of remaining problems.
remainingProblems :: Tc Int
remainingProblems = do
  s <- get
  return $ length (problems s)
