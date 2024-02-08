module Refactoring.AddParam (AddParamArgs (..), addParam) where

import Lang
  ( CtorItem (..),
    DataItem (..),
    Item (..),
    Program (..),
    Term (..),
    TermValue (..),
    Type,
    DeclItem (..),
    Var (..),
    appToList,
    listToApp,
    listToPiType,
    piTypeToList,
    Pat (..),
    Clause (..),
    genTerm,
    mapTerm,
    MapResult (..)
  )
import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupExprArg, lookupIdxArg, lookupNameArg)
import Data.Char (toLower)

-- TODO: Check that the resTerm is of the right type
-- TODO: Update usage sites

-- Arguments to the specialise constructor refactoring.
data AddParamArgs = AddParamArgs
  { -- | The name of the function to add param to
    addParamFuncName :: String,
    -- | The position of the index to add to (count from LEFT, add before i)
    addParamIndexPos :: Int,  
    -- | The type of the new param
    addParamNewTerm :: Term
  }

instance FromRefactorArgs AddParamArgs where
  fromRefactorArgs args =
    AddParamArgs
      <$> lookupNameArg "func" args
      <*> lookupIdxArg "index" args
      <*> lookupExprArg "type" args

-- | Specialise a constructor at a given index to a given term.
addParam :: AddParamArgs -> Program -> Refact Program
addParam args (Program items) =
  return $
    Program
      ( map
          ( \item ->
              case item of
                (Decl d) | declName d == addParamFuncName args -> Decl (addParam_func d)
                _ -> item
          )
          items
      ) --TODO: update usesites of f elsewhere: not implemented
  where 
    addParam_func:: DeclItem -> DeclItem 
    addParam_func d = 
      let (tyList, outTy) = piTypeToList (declTy d)
          (l,r) = splitAt (addParamIndexPos args) tyList 
          newTyList= l ++ ((Var "newParamV" 0 ,addParamNewTerm args ):r)
          newSig = listToPiType (newTyList, outTy)
          in d {declTy =newSig, declClauses = map (addParam_cl (declName d)) (declClauses d)}
    --deals with equations
    addParam_cl:: String -> Clause -> Clause
    addParam_cl funcName (Clause pats term) = 
      Clause (addParam_eqnlhs pats) (mapTerm  (addParam_eqnrhs funcName) term)
    addParam_cl funcName (ImpossibleClause pats) = ImpossibleClause (addParam_eqnlhs pats)
    --add pat var
    addParam_eqnlhs:: [Pat] -> [Pat]
    addParam_eqnlhs pats = 
       let (l,r) = splitAt (addParamIndexPos args) pats 
           in l ++ ((genTerm (V (Var "patV" 0))):r)
    --add holes to recursive calls
    addParam_eqnrhs:: String -> Term -> MapResult Term
    addParam_eqnrhs fName (Term (App term1 term2) termDat ) =
      let (outerTerm, innerTerms) = appToList (Term (App term1 term2) termDat)
        in case termValue (outerTerm) of
            Global str ->
              if str == fName
                then
                  let newInnerTerms = addHolesToPosns ("addParamHole_") innerTerms ([addParamIndexPos args])
                   in Replace (listToApp (outerTerm, newInnerTerms))
                else Continue
            term -> Continue
    addParam_eqnrhs fName term = Continue
    --add holes
    addHolesToPosns :: String -> [Term] -> [Int] -> [Term]
    addHolesToPosns holeNamePrefix termList [] = termList
    addHolesToPosns holeNamePrefix termList (i : is) =
      let (l, r) = splitAt (i+1) termList
          stringPrefix = if r == [] then removeSpaces (show (last l)) else removeSpaces (show (head r))
          newVar = Var (holeNamePrefix ++ stringPrefix ++ show i) 0
          addedOne = l ++ (genTerm (Hole newVar)) : r
       in addHolesToPosns holeNamePrefix addedOne [j + 1 | j <- is]
    removeSpaces :: String -> String
    removeSpaces = filter (\c -> (c /= ' '))


-- stack run -- -r examples/testAddParams.fluid -n add-param -a 'func=f, index=0, type =`Nat`'
-- stack run -- -r examples/example3.fluid -n add-param -a 'func=lookUpVar, index=0, type =`List Nat`'