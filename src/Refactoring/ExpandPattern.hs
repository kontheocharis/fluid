module Refactoring.ExpandPattern (expandPattern) where

import Control.Monad (replicateM)
import Lang
import Refactoring.TraverseUtils
import Refactoring.Utils (FromRefactorArgs (..), Refact, freshVar, lookupIdxArg, lookupNameArg, lookupPositionArg)

-- Arguments to the enhance patterns refactoring.
data ExpandPatternArgs = ExpandPatternArgs
  { -- | The position of the pattern to enhance.
    -- enhancePatSourcePos :: Pos
    addParamFuncName :: String,
    -- | The position of the index to add to (count from LEFT, add before i)
    addParamIndexPos :: Int
  }

instance FromRefactorArgs ExpandPatternArgs where
  fromRefactorArgs args =
    ExpandPatternArgs
      <$> lookupNameArg "func" args
      <*> lookupIdxArg "index" args

-- stack run -- -r D:\Papers\fluid\app\Examples\Test2.fluid -n enhance-pats -a "pos=6:3"

-- Given a constructor name and number of parameters it takes, return a pattern
-- that matches the constructor, with fresh variables for each parameter.
buildPat :: (String, Int) -> Refact TermValue
buildPat (name, num)
  | name == "," = do
      args <- replicateM num (freshVar "x")
      return (Pair ((genTerm . V) (args !! 0)) ((genTerm . V) (args !! 1)))
  | name == "::" = do
      args <- replicateM num (freshVar "x")
      return . termValue $ listToApp ((genTerm . V) (head args), ((Term (Global name) emptyTermData) : (map (genTerm . V) (tail args))))
  | otherwise = do
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

stringToCtrs ty prog
  | ty == "List" = [("::", 2), ("[]", 0)]
  | ty == "Sigma" = [(",", 2)]
  | otherwise = case stringToDataItem ty prog of
      Just it -> getNamesAndParams (typeToCtrs it)

-- transformClauses :: [Clause] -> [Clause]
transformClauses _ _ [] = return []
transformClauses index prog (Clause pats term loc : clauses) =
  let (Term t d) = pats !! index
      (Just ty) = getTypeName (Term t d)
      ctrsInfo = stringToCtrs ty prog
   in do
        newTerms <- mapM buildPat ctrsInfo
        newCls <- replaceTerms t newTerms (Clause pats term loc) (termToId t)
        -- let clauses' = insertClauses clauses c newCls
        clauses' <- transformClauses index prog clauses
        return (newCls ++ clauses')
transformClauses index prog (c : cs) = do
  clauses' <- transformClauses index prog cs
  return (c : clauses')

expandPattern :: ExpandPatternArgs -> Program -> Refact Program
expandPattern (ExpandPatternArgs n i) prog@(Program items) =
  -- error (show prog)
  let -- (Just (Term t d)) = locToTerm p prog
      (Just (DeclItem declName declTy clauses l)) = stringToDecl n prog
   in do
        clauses' <- transformClauses i prog clauses
        prog' <- replaceDeclItem (DeclItem declName declTy clauses l) (DeclItem declName declTy clauses' l) prog
        return prog'

{-
      clauses = nameToClauses prog

      -- (Just c) = termToClause (Term t d) prog
      (Just (DeclItem declName declTy clauses l)) = termToDeclItem (Term t d) prog
      (Just ty) = getTypeName (Term t d)
      ctrsInfo  = stringToCtrs ty prog
      -- ctrs = typeToCtrs it
      -- ctrsInfo = getNamesAndParams ctrs
   in do
        newTerms <- mapM buildPat ctrsInfo
        newCls <- replaceTerms t newTerms c (termToId t)
        let clauses' = insertClauses clauses c newCls
        prog' <- replaceDeclItem (DeclItem declName declTy clauses l) (DeclItem declName declTy clauses' l) prog
        -- error (show d)

        return prog'
-}
