module Refactoring.EnhancePatterns (enhancePatsRefac) where

import Lang

import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupExprArg, lookupIdxArg, lookupNameArg)


import Data.List

-- Arguments to the enhance patterns refactoring.
data EnhancePatsArgs = EnhancePatsArgs
  { -- | The position of the pattern to enhance.
    enhancePatIndexPos :: Int
  }

instance FromRefactorArgs EnhancePatsArgs where
  fromRefactorArgs args =
    EnhancePatsArgs
      <$> lookupIdxArg "index" args
      

enhancePatsRefac :: EnhancePatsArgs -> Program -> Refact Program
enhancePatsRefac args (Program items) = return (Program items)


