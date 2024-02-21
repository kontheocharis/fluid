{-# LANGUAGE LambdaCase #-}

module Refactoring.IdentifyImpossibles (IdentifyImpossiblesArgs, identifyImpossibles) where

import Checking.Context (TcState (..), runTc)
import Checking.Typechecking (checkProgram)
import Control.Monad.Except (MonadError (..))
import Control.Monad.State (MonadState (..))
import Lang (Clause (..), DeclItem (DeclItem), Item (..), Program (..))
import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupFlagArg, lookupNameArg)

data IdentifyImpossiblesArgs = IdentifyImpossiblesArgs
  { -- | The name of the decl to identify impossibles in
    identifyImpossiblesDeclName :: String,
    -- \| Whether to also remove impossibles
    identifyImpossiblesRemove :: Bool
  }

instance FromRefactorArgs IdentifyImpossiblesArgs where
  fromRefactorArgs args =
    IdentifyImpossiblesArgs
      <$> lookupNameArg "decl" args
      <*> lookupFlagArg "remove" args

-- | Identify impossibles in a decl.
identifyImpossibles :: IdentifyImpossiblesArgs -> Program -> Refact Program
identifyImpossibles (IdentifyImpossiblesArgs n alsoRemove) program = do
  let result = runTc $ do
        s <- get
        put $ s {identifyImpossiblesIn = [n]}
        checkProgram program
  case result of
    Left e -> throwError $ show e
    Right (Program p, _) -> do
      if alsoRemove
        then return $ Program (removeImpossibles p)
        else return $ Program p
  where
    removeImpossibles :: [Item] -> [Item]
    removeImpossibles ((Decl (DeclItem n' ty cl loc) : xs))
      | n == n' =
          let cl' = filter (\case ImpossibleClause _ _ -> False; _ -> True) cl
           in (Decl (DeclItem n' ty cl' loc) : xs)
    removeImpossibles ((x : xs)) = x : removeImpossibles xs
    removeImpossibles [] = []
