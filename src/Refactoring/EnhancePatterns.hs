module Refactoring.EnhancePatterns (enhancePatsRefac) where

import Lang

import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupPositionArg)
import Refactoring.TraverseUtils

import Interface.Pretty

import Data.List
import Debug.Trace

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

-- stack run -- -r D:\Papers\fluid\app\Examples\Test2.fluid -n enhance-pats -a "pos=6:3"


-- given a Type, return its constructors and number of parameters for each constructor
{-
getConstructorsAndParams :: TermValue -> [(String, Int)]
getConstructorsAndParams (ListT x) = [("Nil", 0), (Cons, 2)]
getConstructorsAndParams (Global g) = error (show g)
-}

buildPat2 :: Int -> TermValue 
buildPat2 1 = V (Var ("x" ++ "1") 0)
buildPat2 n = App (Term (V (Var ("x" ++ (show n)) 0)) emptyTermData) (Term (buildPat2 (n-1)) emptyTermData)

buildPat :: (String, Int) -> TermValue 
buildPat (name, num) = 
     App (Term (Global name) emptyTermData) (Term (buildPat2 num) emptyTermData)

countParams :: Int -> TermValue -> Int 
countParams n (PiT x (Term ty d) (Term t d2)) = countParams (n+1) t 
countParams n c =  n 

-- for each constructor, return its name and number of parameters it takes
getNamesAndParams :: [CtorItem] -> [(String, Int)]
getNamesAndParams [] = []
getNamesAndParams ((CtorItem n (Term ty d1) d2):ctrs) 
   = let count = countParams 0 ty 
     in (n, count):getNamesAndParams ctrs 


replaceTerms term [] c id = return []
replaceTerms term (t:ts) c id =
    do cs  <- replaceTerms term ts c id 
       c   <- replaceTerm term t c 
       c' <- replaceVar term t id c 
       return (c':cs)


enhancePatsRefac :: EnhancePatsArgs -> Program -> Refact Program
enhancePatsRefac (EnhancePatsArgs p) prog@(Program items) =  -- error (show prog)
    let (Just (Term t d)) = locToTerm p prog
        (Just c) = termToClause (Term t d) prog
        (Just (DeclItem declName declTy clauses l)) = termToDeclItem (Term t d) prog
        (Just ty) = getTypeName (Term t d) prog
        (Just it) = stringToDataItem ty prog 
        ctrs = typeToCtrs it
        ctrsInfo = getNamesAndParams ctrs
        newTerms = map buildPat ctrsInfo 
    in trace (concat (map printTermValue newTerms)) $ 
           do newCls <- replaceTerms t newTerms c (termToId t)
              let clauses' = insertClauses clauses c newCls
              prog' <- replaceDeclItem (DeclItem declName declTy clauses l) (DeclItem declName declTy clauses' l)  prog 
              error $ printProgram prog'

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



