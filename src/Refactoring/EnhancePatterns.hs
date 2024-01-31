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
      
getPos :: Maybe Pos -> Pos 
getPos Nothing = error "Location in source code not found!"
getPos (Just p) = p


refacClause :: [Clause] -> Refact [Clause]
refacClause clauses = return clauses


enhancePatsRefac :: EnhancePatsArgs -> Program -> Refact Program
enhancePatsRefac (EnhancePatsArgs p) (Program items) =   
  return 
    (Program 
      (map (\item -> 
          case item of
              (Decl (DeclItem name ty clauses)) -> error "bob"
              {-   (map (\cl -> 
                  case cl of 
                    (Clause pats t) -> error "bob"
                      {- map (\pat ->
                        case pat of 
                          (Term (V (Var name id)) d) -> if getPos (startPos (getLoc d)) == p 
                                                          then error "here" 
                                                          else error "other" -- Term (V (Var name id))  d
                          p -> p
                      ) pats -}
                  --   c -> (Decl (DeclItem name ty clauses))
                ) clauses ) 
              d -> d -}
      ) items 
      ))


{-              (Decl decl) -> if (declName decl) == (removeMaybeFuncName args) then 
                                  Decl (removeMaybe_func decl)
                              else 
                                  Decl decl
              (Data dat) -> Data dat        
-}



