module Refactoring.AddParam (AddParamArgs (..), addParam) where

import Lang
  ( Clause (..),
    DeclItem (..),
    Item (..),
    MapResult (..),
    Pat,
    Program (..),
    Term (..),
    TermValue (..),
    Var (..),
    appToList,
    genTerm,
    listToApp,
    listToPiType,
    mapTerm,
    piTypeToList,
  )
import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupExprArg, lookupIdxArg, lookupNameArg, slugify)

-- TODO: Check that the resTerm is of the right type
-- TODO: Update usage sites

-- Arguments to the specialise constructor refactoring.
data AddParamArgs = AddParamArgs
  { -- | The name of the function to add param to
    addParamFuncName :: String,
    -- | The position of the index to add to (count from LEFT, add before i)
    addParamIndexPos :: Int,
    -- | The type of the new param
    addParamNewTerm :: Term,
    -- | The name of the new param
    addParamParamName :: String
  }

instance FromRefactorArgs AddParamArgs where
  fromRefactorArgs args =
    AddParamArgs
      <$> lookupNameArg "func" args
      <*> lookupIdxArg "index" args
      <*> lookupExprArg "type" args
      <*> lookupNameArg "name" args

-- | Specialise a constructor at a given index to a given term.
addParam :: AddParamArgs -> Program -> Refact Program
addParam args (Program items) =
  let addedParam =
        map
          ( \item ->
              case item of
                (Decl d) | declName d == addParamFuncName args -> Decl (addParam_func d)
                _ -> item
          )
          items
   in return (Program (map updateUseCase addedParam))
  where
    addParam_func :: DeclItem -> DeclItem
    addParam_func d =
      let (tyList, outTy) = piTypeToList (declTy d)
          (l, r) = splitAt (addParamIndexPos args) tyList
          newTyList = l ++ ((Var (addParamParamName args) 0, addParamNewTerm args) : r)
          newSig = listToPiType (newTyList, outTy)
       in d {declTy = newSig, declClauses = map addParam_cl (declClauses d)}

    -- deals with equations
    addParam_cl :: Clause -> Clause
    addParam_cl (Clause pats term l) =
      Clause (addParam_eqnlhs pats) term l
    addParam_cl (ImpossibleClause pats l) = ImpossibleClause (addParam_eqnlhs pats) l

    -- add pat var
    addParam_eqnlhs :: [Pat] -> [Pat]
    addParam_eqnlhs pats =
      let (l, r) = splitAt (addParamIndexPos args) pats
       in l ++ (genTerm (V (Var (addParamParamName args) 0)) : r)

    -- add holes to recursive calls
    addParam_eqnrhs :: Term -> MapResult Term
    addParam_eqnrhs (Term (App term1 term2) termDat) =
      let (outerTerm, innerTerms) = appToList (Term (App term1 term2) termDat)
       in case termValue outerTerm of
            Global str ->
              if str == addParamFuncName args
                then
                  let newInnerTerms = addHolesToPosns "addParamHole_" innerTerms [addParamIndexPos args]
                   in Replace (listToApp (outerTerm, newInnerTerms))
                else Continue
            _ -> Continue
    addParam_eqnrhs _ = Continue

    -- add holes
    addHolesToPosns :: String -> [Term] -> [Int] -> [Term]
    addHolesToPosns _ termList [] = termList
    addHolesToPosns holeNamePrefix termList (i : is) =
      let (l, r) = splitAt i termList
          stringPrefix = if null r then slugify (last l) else slugify (head r)
          newVar = Var (holeNamePrefix ++ stringPrefix ++ show i) 0
          addedOne = l ++ genTerm (Hole newVar) : r
       in addHolesToPosns holeNamePrefix addedOne [j + 1 | j <- is]

    -- update usecase of f elsewhere
    updateUseCase :: Item -> Item
    updateUseCase (Decl d) = Decl d {declClauses = map updateUseCase_cl (declClauses d)}
    updateUseCase (Data d) = Data d
    updateUseCase_cl :: Clause -> Clause
    updateUseCase_cl (Clause pats term l) =
      Clause pats (mapTerm addParam_eqnrhs term) l
    updateUseCase_cl (ImpossibleClause pats l) = ImpossibleClause pats l

-- stack run -- -r examples/testAddParams.fluid -n add-param -a 'func=f, index=0, type =`Nat`'
-- stack run -- -r examples/example3.fluid -n add-param -a 'func=lookUpVar, index=0, type =`List Nat`'
