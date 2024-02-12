module Refactoring.IdentifyImpossibles (IdentifyImpossiblesArgs, identifyImpossibles) where

import Checking.Context (TcState (..), runTc)
import Checking.Typechecking (checkProgram)
import Control.Monad.Except (MonadError (..))
import Control.Monad.State (MonadState (..))
import Lang (Program)
import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupNameArg)

newtype IdentifyImpossiblesArgs = IdentifyImpossiblesArgs
  { -- | The name of the decl to identify impossibles in
    identifyImpossiblesDeclName :: String
  }

instance FromRefactorArgs IdentifyImpossiblesArgs where
  fromRefactorArgs args =
    IdentifyImpossiblesArgs
      <$> lookupNameArg "decl" args

-- | Identify impossibles in a decl.
identifyImpossibles :: IdentifyImpossiblesArgs -> Program -> Refact Program
identifyImpossibles (IdentifyImpossiblesArgs n) program = do
  let result = runTc $ do
        s <- get
        put $ s {identifyImpossiblesIn = [n]}
        checkProgram program
  case result of
    Left e -> throwError $ show e
    Right (p, _) -> return p
