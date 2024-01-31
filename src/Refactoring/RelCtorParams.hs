module Refactoring.RelCtorParams (RelCtorArgs (..), relCtorParams) where

import Lang
  ( CtorItem (..),
    DataItem (..),
    Item (..),
    Program (..),
    Term (..),
    TermValue (..),
    Type,
    Var (..),
    appToList,
    listToApp,
    listToPiType,
    piTypeToList,
    genTerm
  )
import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupExprArg, lookupIdxArg, lookupNameArg)


-- Arguments to the specialise constructor refactoring.
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
      <*> Just [1,2] --lookupIdsArg "inds" args   --TODO update to allow for list
      <*> lookupExprArg "reln" args



piTypeToListWithDummy :: Type -> [(Var, Type)]
piTypeToListWithDummy ty = 
    let (tys,rTy) = piTypeToList ty 
        in tys ++ [(Var "DummyVar" 0,rTy)]


listWithDummyToPiType :: ([(Var, Type)]) -> Type
listWithDummyToPiType l = 
    listToPiType (take ((length l)-1) l ,snd (last l) )


getVarsAtPosns:: [(Var, Type)] -> [Int] -> [Var]
getVarsAtPosns varTyList = foldr (\x acc -> (fst (varTyList!!x):acc)) []

insertAfter::  [(Var, Type)] -> Int -> (Var,Type) -> [(Var, Type)]
insertAfter varTyList i varTy = 
    let (l,r) = splitAt (i+1) varTyList
        in l ++ (varTy:r)

{-
data RefactState = RefactState {varCounter :: Int}
 
data Refact a = State RefactState a
 

-- | Get a fresh variable.
freshVar :: Refact Var
freshVar = do
  s <- get
  let h = varCounter s
  put $ s {varCounter = h + 1}
  return $ Var ("v" ++ show h) h
-}

 

relCtorParams :: RelCtorArgs -> Program -> Refact Program
relCtorParams args (Program items) = 
    return $
        Program 
            (map (\item -> case item of
                                Data d | dataName d == relCtorParamsDataName args -> Data (relCtorParams_data d)
                                _ -> item
                )
                items
            )
    --todo: update usecase of cosntructor
    where 
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
        relCtorParams_ctor :: CtorItem -> CtorItem
        relCtorParams_ctor c =
            let tys = piTypeToListWithDummy (ctorItemTy c)
                inds = map (\i -> (length tys) - i -1) (relCtorParamsIndsPos args) 
                varsToRelate = getVarsAtPosns tys inds
                newVarTy = makeRelationParam varsToRelate 
                inserted = insertAfter tys (maximum inds) newVarTy
                in c {ctorItemTy = listWithDummyToPiType inserted}
        makeRelationParam:: [Var] -> (Var, Type)
        makeRelationParam vars = 
            let termList = map (\v -> genTerm (V v)) vars 
                in (Var "newRelParam" 0, listToApp (relCtorParamsNewTerm args, termList))
          