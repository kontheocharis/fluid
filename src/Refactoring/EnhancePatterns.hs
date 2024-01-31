module Refactoring.EnhancePatterns (enhancePatsRefac) where

import Lang

import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupPositionArg)
import Refactoring.TraverseUtils

import Data.List

-- Arguments to the enhance patterns refactoring.
data EnhancePatsArgs = EnhancePatsArgs
  { -- | The position of the pattern to enhance.
    enhancePatSourcePos :: Pos
  }

instance FromRefactorArgs EnhancePatsArgs where
  fromRefactorArgs args =
    EnhancePatsArgs
      <$> lookupPositionArg "pos" args
      



refacClause :: [Clause] -> Refact [Clause]
refacClause clauses = return clauses


enhancePatsRefac :: EnhancePatsArgs -> Program -> Refact Program
enhancePatsRefac (EnhancePatsArgs p) prog@(Program items) =  -- error (show prog)
  do 
    let t = locToTerm p prog
    error (show t)


{-              (Decl decl) -> if (declName decl) == (removeMaybeFuncName args) then 
                                  Decl (removeMaybe_func decl)
                              else 
                                  Decl decl
              (Data dat) -> Data dat        
-}



