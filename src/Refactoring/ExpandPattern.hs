module Refactoring.ExpandPattern (expandPattern) where

import Control.Monad (replicateM)
import Lang
import Refactoring.TraverseUtils
import Refactoring.Utils (FromRefactorArgs (..), Refact, freshVar, lookupPositionArg)

-- Arguments to the enhance patterns refactoring.
newtype ExpandPatternArgs = ExpandPatternArgs
  { -- | The position of the pattern to enhance.
    enhancePatSourcePos :: Pos
  }

instance FromRefactorArgs ExpandPatternArgs where
  fromRefactorArgs args =
    ExpandPatternArgs
      <$> lookupPositionArg "pos" args

-- stack run -- -r D:\Papers\fluid\app\Examples\Test2.fluid -n enhance-pats -a "pos=6:3"

-- Given a constructor name and number of parameters it takes, return a pattern
-- that matches the constructor, with fresh variables for each parameter.
buildPat :: (String, Int) -> Refact TermValue
buildPat (name, num) = do
  args <- replicateM num (freshVar "x")
  return . termValue $ listToApp (Term (Global name) emptyTermData, map (genTerm . V) args)

-- for each constructor, return its name and number of parameters it takes
getNamesAndParams :: [CtorItem] -> [(String, Int)]
getNamesAndParams = map (\(CtorItem n ty _) -> (let (params, _) = piTypeToList ty in (n, length params)))

replaceTerms term [] c id = return []
replaceTerms term (t : ts) c id =
  do
    cs <- replaceTerms term ts c id
    c <- replaceTerm term t c
    c' <- replaceVar term t id c
    return (c' : cs)

expandPattern :: ExpandPatternArgs -> Program -> Refact Program
expandPattern (ExpandPatternArgs p) prog@(Program items) =
  -- error (show prog)
  let (Just (Term t d)) = locToTerm p prog
      (Just c) = termToClause (Term t d) prog
      (Just (DeclItem declName declTy clauses l)) = termToDeclItem (Term t d) prog
      (Just ty) = getTypeName (Term t d) prog
      (Just it) = stringToDataItem ty prog
      ctrs = typeToCtrs it
      ctrsInfo = getNamesAndParams ctrs
   in do
        newTerms <- mapM buildPat ctrsInfo
        newCls <- replaceTerms t newTerms c (termToId t)
        let clauses' = insertClauses clauses c newCls
        prog' <- replaceDeclItem (DeclItem declName declTy clauses l) (DeclItem declName declTy clauses' l) prog
        return prog'
