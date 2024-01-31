module Refactoring.RelCtorParams (RelCtorArgs (..), relCtorParams) where

import Lang
  ( CtorItem (..),
    DataItem (..),
    DeclItem (..),
    Item (..),
    Program (..),
    Term (..),
    TermValue (..),
    Type,
    Var (..),
    Clause (..),
    Pat (..),
    appToList,
    listToApp,
    listToPiType,
    piTypeToList,
    genTerm
  )
import Refactoring.Utils (FromRefactorArgs (..), Refact, RefactState, lookupExprArg, lookupIdxListArg, lookupNameArg, freshVar)
import Control.Monad.State (MonadState (get), State, put, evalState, runState)



-- Arguments to the refactoring.
data RelCtorArgs = RelCtorArgs
  { -- | The name of the data type to specialise.
    relCtorParamsDataName :: String,
    -- | The name of the constructor to specialise.
    relCtorParamsCtorName :: String,
    -- | The position of the index to specialise.
    relCtorParamsIndsPos :: [Int],
    -- | The term to specialise the index to.
    relCtorParamsNewTerm :: Term
  }

instance FromRefactorArgs RelCtorArgs where
  fromRefactorArgs args =
    RelCtorArgs
      <$> lookupNameArg "data" args
      <*> lookupNameArg "ctor" args
      <*> lookupIdxListArg "inds" args  
      <*> lookupExprArg "reln" args


--like piTypeToList, but as a (var,type) list, so it's easier to work with
piTypeToListWithDummy :: Type -> [(Var, Type)]
piTypeToListWithDummy ty = 
    let (tys,rTy) = piTypeToList ty 
        in tys ++ [(Var "DummyVar" 0,rTy)]

--like listToPiType, but as a (var,type) list, so it's easier to work with
listWithDummyToPiType :: ([(Var, Type)]) -> Type
listWithDummyToPiType l = 
    listToPiType (take ((length l)-1) l ,snd (last l) )


--insert into a list after given index
insertAfter::  [a] -> Int -> a -> [a]
insertAfter varTyList i varTy = 
    let (l,r) = splitAt (i+1) varTyList
        in l ++ (varTy:r)


--check if App term is given data
isAppData:: String -> Term -> Bool 
isAppData dName ty = 
    let appList = appToList ty 
        in termValue (fst appList) == Global dName


--check that function has a type (given as string name) as a param
funcHasTyAsParam:: DeclItem -> String -> Bool 
funcHasTyAsParam decl dName =
    let (tyList, retTy) = piTypeToList (declTy decl) 
        in  any (isAppData dName) ((retTy):(map (\t -> (snd t)) tyList))  


--relating params of constructor refactoring
relCtorParams :: RelCtorArgs -> Program -> Refact Program
relCtorParams args (Program items) = 
    let newP = Program 
                    (map (\item -> case item of
                                        Data d | dataName d == relCtorParamsDataName args -> Data (relCtorParams_data d)
                                        _ -> item
                        )
                        items
                    )
        usecaseUpdate = updateUsecase newP 
        in return $ usecaseUpdate
    where 
        --find ctor in data, refactor ctor
        relCtorParams_data :: DataItem -> DataItem
        relCtorParams_data d =
            d
                { dataCtors =
                    map
                    ( \c ->
                        if ctorItemName c == relCtorParamsCtorName args
                            then relCtorParams_ctor c
                            else c
                    )
                    (dataCtors d)
                }
        --relate params of ctor
        relCtorParams_ctor :: CtorItem -> CtorItem
        relCtorParams_ctor c =
            let tys = piTypeToListWithDummy (ctorItemTy c)
                inds = map (\i -> (length tys) - i -1) (relCtorParamsIndsPos args) 
                varsToRelate = foldr (\x acc -> (fst (tys!!x):acc)) [] inds
                newVarTy = makeRelationParam varsToRelate 
                inserted = insertAfter tys (maximum inds) newVarTy
                in c {ctorItemTy = listWithDummyToPiType inserted}
        --get var,type for the new relation param
        makeRelationParam:: [Var] -> (Var, Type)
        makeRelationParam vars = 
            let termList = map (\v -> genTerm (V v)) vars 
                in (Var "relParamV" 0, listToApp (relCtorParamsNewTerm args, termList)) -- todo: get fresh var
        --update usecase (for now, as params of functions only)
        updateUsecase :: Program -> Program 
        updateUsecase (Program items) =
            Program (map (\item -> case item of
                                        Decl d -> if (funcHasTyAsParam d (relCtorParamsDataName args)) then
                                                    Decl d {declClauses = map updateUsecase_cl (declClauses d)} 
                                                  else 
                                                    Decl d
                                        _ -> item
                        )
                        items
                    )
        --update usecase in a clause
        updateUsecase_cl :: Clause -> Clause
        updateUsecase_cl (Clause lhsPats rhsTerm) = Clause (map updateUsecase_pat lhsPats) (updateUsecase_rhs rhsTerm)
        updateUsecase_cl (ImpossibleClause lhsPats) = ImpossibleClause (map updateUsecase_pat lhsPats)
        --update use of ctor in pattern (lhs of equations) -> add additional variable
        updateUsecase_pat:: Pat -> Pat
        updateUsecase_pat pat = if isAppData (relCtorParamsCtorName args) pat then   
                                            let (outerTerm, argList) = appToList pat
                                                posnToInsert =  (length argList) - minimum (relCtorParamsIndsPos args)  
                                                varInserted = insertAfter argList posnToInsert (genTerm (V (Var ("vrel_" ++ (show posnToInsert)) 0)))  
                                                in (listToApp (outerTerm,varInserted)) 
                                         else 
                                            pat               
        --update use of ctor in rhs of equations -> add holes
        updateUsecase_rhs :: Term -> Term
        updateUsecase_rhs (Term (Case caseTerm patTermList) termDat) = 
            (Term (Case caseTerm (map (\pt -> (updateUsecase_pat (fst pt), updateUsecase_rhs (snd pt)) ) patTermList)) termDat)  
        updateUsecase_rhs (Term (App term1 term2) termDat) = 
            let (outerTerm, argList) = appToList (Term (App term1 term2) termDat) in 
                if termValue outerTerm == Global (relCtorParamsCtorName args) then 
                    let posnToInsert =  (length argList) - minimum (relCtorParamsIndsPos args)  
                        holeInserted = insertAfter argList posnToInsert (genTerm (Hole (Var ("vrel_" ++ (show posnToInsert)) 0)))  
                        in (listToApp (outerTerm, holeInserted)) 
                else 
                    (Term (App (updateUsecase_rhs term1) (updateUsecase_rhs term2)) termDat)
        updateUsecase_rhs term = term
        
