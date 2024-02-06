module Refactoring.SpecCtor (SpecCtorArgs (..), specCtor) where

import Lang
  ( CtorItem (..),
    DataItem (..),
    Item (..),
    Program (..),
    Term (..),
    Type,
    appToList,
    listToApp,
    listToPiType,
    piTypeToList,
  )
import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupExprArg, lookupIdxArg, lookupNameArg)

-- TODO: Check that the resTerm is of the right type
-- TODO: Update usage sites

-- Arguments to the specialise constructor refactoring.
data SpecCtorArgs = SpecCtorArgs
  { -- | The name of the data type to specialise.
    specCtorDataName :: String,
    -- | The name of the constructor to specialise.
    specCtorCtorName :: String,
    -- | The position of the index to specialise.
    specCtorIndexPos :: Int,
    -- | The term to specialise the index to.
    specCtorNewTerm :: Term
  }

instance FromRefactorArgs SpecCtorArgs where
  fromRefactorArgs args =
    SpecCtorArgs
      <$> lookupNameArg "data" args
      <*> lookupNameArg "ctor" args
      <*> lookupIdxArg "index" args
      <*> lookupExprArg "term" args

-- | Specialise a constructor at a given index to a given term.
specCtor :: SpecCtorArgs -> Program -> Refact Program
specCtor args (Program items) =
  return $
    Program
      ( map
          ( \item ->
              case item of
                (Data d) | dataName d == specCtorDataName args -> Data (specCtorDataItem d)
                _ -> item
          )
          items
      )
  where
    -- \| Handle a data item.
    specCtorDataItem :: DataItem -> DataItem
    specCtorDataItem d =
      d
        { dataCtors =
            map
              ( \c ->
                  if ctorItemName c == specCtorCtorName args
                    then specCtorItem c
                    else c
              )
              (dataCtors d)
        }

    -- \| Handle a constructor item in the correct data item.
    specCtorItem :: CtorItem -> CtorItem
    specCtorItem c =
      let (tys, ret) = piTypeToList (ctorItemTy c)
       in c {ctorItemTy = listToPiType (tys, specCtorRet ret)}

    -- \| Handle the return type of the correct constructor.
    specCtorRet :: Type -> Type
    specCtorRet ret =
      let (t, ts) = appToList ret
       in listToApp
            ( t,
              zipWith (\i a -> if i == specCtorIndexPos args then specCtorNewTerm args else a) [0 ..] ts
            )
