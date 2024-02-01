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

-- given a Type, return its constructors and number of parameters for each constructor
{-
getConstructorsAndParams :: TermValue -> [(String, Int)]
getConstructorsAndParams (ListT x) = [("Nil", 0), (Cons, 2)]
getConstructorsAndParams (Global g) = error (show g)
-}

enhancePatsRefac :: EnhancePatsArgs -> Program -> Refact Program
enhancePatsRefac (EnhancePatsArgs p) prog@(Program items) =  -- error (show prog)
  do 
    let (Just t) = locToTerm p prog
    let c = termToClause t prog
    error (show c)
    
{-
    case t of 
      (Just (Term (V (Var n id)) (TermData l (Term ty d2)))) -> 
             case ty of
                (ListT ty3) -> --- (Just (Term (V (Var n id)) (TermData l (Term ty d2))))
               
      _                     -> error "error: please select a pattern variable to expand"
-}

{-              (Decl decl) -> if (declName decl) == (removeMaybeFuncName args) then 
                                  Decl (removeMaybe_func decl)
                              else 
                                  Decl decl
              (Data dat) -> Data dat        
-}



