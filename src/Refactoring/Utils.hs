{-# LANGUAGE LambdaCase #-}

module Refactoring.Utils
  ( RefactState,
    Refact,
    runRefact,
    evalRefact,
    freshVar,
    RefactorArgKind (..),
    RefactorArgs (..),
    FromRefactorArgs (..),
    lookupNameArg,
    lookupIdxArg,
    lookupIdxListArg,
    lookupPositionArg,
    lookupExprArg,
  )
where

import Control.Monad.State (MonadState (get), State, put, runState)
import Lang (Pos, Term, Var (..))

-- | The state kept during a refactoring.
newtype RefactState = RefactState {varCounter :: Int}

-- | The initial refactoring state.
emptyRefactState :: RefactState
emptyRefactState = RefactState 0

-- | The refactoring monad.
type Refact a = State RefactState a

-- | Run a refactoring.
runRefact :: Refact a -> RefactState -> (a, RefactState)
runRefact = runState

-- | Run a refactoring in a blank state, returning only the result.
evalRefact :: Refact a -> a
evalRefact r = fst $ runRefact r (RefactState 0)

-- | Get a fresh variable, given a prefix
freshVar :: String -> Refact Var
freshVar prefix = do
  s <- get
  let h = varCounter s
  put $ s {varCounter = h + 1}
  return $ Var (prefix ++ show h) h

-- | The kind of an argument that might be given to a refactoring.
data RefactorArgKind = Name String | Idx Int | Position Pos | Expr Term | IdxList [Int] deriving (Show)

-- | Opaque arguments given to a refactoring as key-value pairs.
--
-- These depend on the refactoring being applied.
newtype RefactorArgs = RefactorArgs [(String, RefactorArgKind)] deriving (Show)

-- | Look up a name argument.
lookupNameArg :: String -> RefactorArgs -> Maybe String
lookupNameArg name (RefactorArgs args) = lookup name args >>= \case Name n -> Just n; _ -> Nothing

-- | Look up an index argument.
lookupIdxArg :: String -> RefactorArgs -> Maybe Int
lookupIdxArg name (RefactorArgs args) = lookup name args >>= \case Idx i -> Just i; _ -> Nothing

-- | Look up a list of indices argument.
lookupIdxListArg :: String -> RefactorArgs -> Maybe [Int]
lookupIdxListArg name (RefactorArgs args) = lookup name args >>= \case IdxList is -> Just is; _ -> Nothing

-- | Look up a position argument.
lookupPositionArg :: String -> RefactorArgs -> Maybe Pos
lookupPositionArg name (RefactorArgs args) = lookup name args >>= \case Position p -> Just p; _ -> Nothing

-- | Look up a term argument.
lookupExprArg :: String -> RefactorArgs -> Maybe Term
lookupExprArg name (RefactorArgs args) = lookup name args >>= \case Expr e -> Just e; _ -> Nothing

-- | Class for types that can be parsed from refactoring arguments.
class FromRefactorArgs a where
  fromRefactorArgs :: RefactorArgs -> Maybe a
