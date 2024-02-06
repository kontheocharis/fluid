module Refactoring.AddIndex2 (addIndex2) where

import Data.List (findIndices)
import Data.Char (toLower)
import Lang
  ( Clause (..),
    CtorItem (..),
    DataItem (..),
    DeclItem (..),
    GlobalName,
    Item (..),
    Pat,
    Program (..),
    Term (..),
    TermValue (..),
    Type,
    Var (..),
    listToPiType,
    piTypeToList, 
    listToApp,
    appToList,
    genTerm,
    MapResult (..),
    mapTerm
  )
import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupExprArg, lookupIdxArg, lookupNameArg)

--------------------------



data AddIndexArgs = AddIndexArgs
  { -- | The name of the data type to specialise.
    addIndDataName :: String,
    -- | The type of the new index
    addIndIndexType :: Term,
    -- | The position  of the new index (count from left!!)
    addIndIndexPos :: Int

  }

instance FromRefactorArgs AddIndexArgs where
  fromRefactorArgs args =
    AddIndexArgs
      <$> lookupNameArg "data" args
      <*> lookupExprArg "type" args
      <*> lookupIdxArg "index" args
     

data ChangedCtorInfo = ChangedCtorInfo 
  {
    changedCtorInfoName :: String, 
    --param added before which position
    changedCtorInfoInds :: [Int]
  }

data ChangedFuncInfo = ChangedFuncInfo 
  {
    changedFuncInfoName :: String, 
    --param added before which position
    changedFuncInfoInds :: [Int]
  }


isMyData :: Type -> String -> Bool
isMyData ty name = case termValue ty of
  Global str ->
    if str == name
      then True
      else False
  term -> False


-- like piTypeToList, but as a (var,type) list, so it's easier to work with
piTypeToListWithDummy :: Type -> [(Var, Type)]
piTypeToListWithDummy ty =
  let (tys, rTy) = piTypeToList ty
   in tys ++ [(Var "DummyVar" 0, rTy)]

-- like listToPiType, but as a (var,type) list, so it's easier to work with
listWithDummyToPiType :: ([(Var, Type)]) -> Type
listWithDummyToPiType l =
  listToPiType (take ((length l) - 1) l, snd (last l))


gather:: [a] -> (a -> (a,  [b]) ) -> ([a] , [b])
gather l f = foldr (\x acc -> let (fx, changed) = f x 
                                              in (fx:(fst acc) , snd acc ++  changed)) ([],[]) l


insertAt_terms :: [Term] -> [(Int, Term)] -> [Term]
insertAt_terms list [] = list
insertAt_terms list ((i, elt) : res) =
  let (l, r) = splitAt (i + 1) list
      addedOne = l ++ [elt] ++ r
   in insertAt_terms addedOne [(j + 1, e) | (j, e) <- res]


removeSpaces:: String -> String
removeSpaces = filter (\c -> (c /=' '))

addIndex2 :: AddIndexArgs -> Program -> Refact Program
addIndex2 args (Program items) = 
  let (nItems, changedCtors) = addIndexToData items
      (nnItems, changedFuncs)  = gather nItems (updateUseSites_item changedCtors)
      --update use sites fo changed functions: not implemented
  in return (Program nnItems)
  where 
    --add index as new params in constructors
    addIndexToData:: [Item] -> ([Item], [ChangedCtorInfo])
    addIndexToData items = gather items (addIndexToData_items)
    -- deals with items
    addIndexToData_items :: Item -> (Item, [ChangedCtorInfo])
    addIndexToData_items (Data d) = 
      if dataName d == addIndDataName args then 
        let (nCtors, changedCtors) = gather (dataCtors d) (addIndexToData_ctor) 
            newTy = insertParam (dataTy d) (addIndIndexPos args) 
            in (Data d {dataTy = newTy, dataCtors = nCtors}, changedCtors)
      else 
        (Data d, [])
    addIndexToData_items d = (d, [])
    --deals with constructors
    addIndexToData_ctor:: CtorItem -> (CtorItem, [ChangedCtorInfo])
    addIndexToData_ctor ctor = 
      let tyList = piTypeToListWithDummy (ctorItemTy ctor) 
          dataParamPosns =  filter (\j -> isMyData (snd (tyList !! j)) (addIndDataName args)) [0 .. (length tyList) - 1]  
          newTy = listWithDummyToPiType (insertParamAndRelate ((map toLower (ctorItemName ctor)) ++ "param_") tyList dataParamPosns)
          changedCtorInfo = ChangedCtorInfo (ctorItemName ctor) dataParamPosns
          in (ctor {ctorItemTy = newTy}, [changedCtorInfo])
    insertParam :: Type -> Int -> Type
    insertParam ty i =  
        let vtList = piTypeToListWithDummy ty
            (l, r) = splitAt i vtList 
            newVar = Var ("newInd" ++ show i) 0
            newList = l ++ ((newVar, addIndIndexType args)):r
            in listWithDummyToPiType newList
    --insert param before indices and relate to next param
    insertParamAndRelate :: String -> [(Var, Type)] -> [Int] -> [(Var, Type)]
    insertParamAndRelate varNamePrefix vtList [] = vtList
    insertParamAndRelate varNamePrefix vtList (i:is) = 
      let (l, r) = splitAt i vtList 
          newVar = Var (varNamePrefix ++ show i) 0
          relatedTerm =  useVarAsInd newVar (head r) 
          addedOne = l ++ ((newVar, addIndIndexType args)):( relatedTerm:(tail r) )
          in insertParamAndRelate varNamePrefix addedOne [ j+1 | j <- is]
    --use var as an index
    useVarAsInd :: Var -> (Var, Type) -> (Var, Type)
    useVarAsInd var (v, ty) = (v, insertAt_appterm (addIndIndexPos args) (genTerm (V var)) ty)
    --add newTerm as the before the ith position of appTerm
    insertAt_appterm :: Int -> Term -> Term -> Term
    insertAt_appterm i newTerm appTerm =
      let (outerTerm, innerTerms) = appToList appTerm
          (l, r) = splitAt (i - 1) innerTerms
      in listToApp (outerTerm, l ++ (newTerm:r))
   --update usage sites of data (only use sites as params pf functions implemented)
    updateUseSites_item:: [ChangedCtorInfo] -> Item -> (Item, [ChangedFuncInfo])
    updateUseSites_item changedCtors (Decl d)  = 
      let (newTy, changedFuncInfo) = updateUseSites_sig (declName d) (declTy d)
          changedEqns = map (updateUseSites_eqn changedCtors (head changedFuncInfo)) (declClauses d)
      in (Decl d {declTy = newTy, declClauses = changedEqns}, changedFuncInfo) --todo: change declClauses
    updateUseSites_item changedCtors item  = (item, [])
    --add params to signature of functions before param of type D
    updateUseSites_sig:: String -> Type -> (Type, [ChangedFuncInfo])
    updateUseSites_sig fname ty = 
      let tyList = piTypeToListWithDummy ty
          dataParamPosns =  filter (\j -> isMyData (snd (tyList !! j)) (addIndDataName args)) [0 .. (length tyList) - 1]  
          newTy = listWithDummyToPiType (insertParamAndRelate (fname ++ "param_") tyList dataParamPosns)
          changedFuncInfo = ChangedFuncInfo fname dataParamPosns
          in (newTy, [changedFuncInfo])
    --update function body 
    updateUseSites_eqn:: [ChangedCtorInfo] -> ChangedFuncInfo -> Clause -> Clause
    updateUseSites_eqn cinfo finfo (ImpossibleClause pats) = ImpossibleClause (updateUseSites_eqnLHS cinfo finfo pats)
    updateUseSites_eqn cinfo finfo (Clause pats term) = Clause (updateUseSites_eqnLHS cinfo finfo pats) (updateUseSites_eqnRHS cinfo finfo term) --todo update eqnrhs
    --update lhs of eqns
    updateUseSites_eqnLHS:: [ChangedCtorInfo] -> ChangedFuncInfo -> [Pat] -> [Pat]
    updateUseSites_eqnLHS cinfo finfo pats =
      insertPatVarAndRelate cinfo ("patvar_") pats (changedFuncInfoInds finfo) 
    --add var at index (changedFuncInfoInds finfo) 
    --if the next pat is in cinfo then: add holes and relate last vat
    insertPatVarAndRelate :: [ChangedCtorInfo] ->  String -> [Pat] -> [Int] -> [Pat]
    insertPatVarAndRelate cinfo varNamePrefix patList [] = patList
    insertPatVarAndRelate cinfo varNamePrefix patList (i:is) = 
      let (l, r) = splitAt i patList 
          newVarTerm = Var (varNamePrefix ++ show i) 0
          in 
            case r of 
              [] -> let addedOne = l ++ [genTerm (V newVarTerm)]
                    in insertPatVarAndRelate cinfo varNamePrefix addedOne [ j+1 | j <- is]
              (rhead:rres) -> let relatedTerm =  relateTerm_eqnLHS cinfo newVarTerm rhead 
                                  addedOne = l ++ (genTerm (V newVarTerm)):(relatedTerm:rres)
                                  in insertPatVarAndRelate cinfo varNamePrefix addedOne [ j+1 | j <- is]
    relateTerm_eqnLHS:: [ChangedCtorInfo] -> Var -> Pat -> Pat
    relateTerm_eqnLHS cinfo newVar pat = 
      let (outerTerm, innerTerms) = appToList pat 
        in case termValue outerTerm of   
          Global str -> let ctorInd = findIndices (\x -> changedCtorInfoName x == str) cinfo
                            dataIndPosn = changedCtorInfoInds (cinfo !! (head ctorInd))
                            addedExtraInds = insertIndToPatVar ("paramforpatvar_" ++ str ++ "_") innerTerms (take (length dataIndPosn -1) dataIndPosn)
                            in listToApp (outerTerm, addedExtraInds ++ [genTerm (V newVar)]) --todo add newVarTerm to the last position
          _ -> pat
    insertIndToPatVar :: String -> [Term] -> [Int] -> [Term]
    insertIndToPatVar varNamePrefix termList [] = termList
    insertIndToPatVar varNamePrefix termList (i:is) = 
       let  (l, r) = splitAt i termList 
            newVar = Var (varNamePrefix ++ show i) 0
            addedOne = l ++ (genTerm (V newVar)):r
            in insertIndToPatVar varNamePrefix addedOne [ j+1 | j <- is]
    updateUseSites_eqnRHS:: [ChangedCtorInfo] -> ChangedFuncInfo -> Term -> Term
    updateUseSites_eqnRHS cinfo finfo term = 
      let funcCallUpdated = mapTerm (addHolesToFuncCalls finfo) term
        in mapTerm (addHolesToCtorCalls cinfo) funcCallUpdated
      --todo: add holes to contructors
    --add holes to all occurrences of function calls in the rhs of eqns
    addHolesToFuncCalls:: ChangedFuncInfo -> Term -> MapResult Term
    addHolesToFuncCalls finfo (Term (App term1 term2) termDat) = 
        let (outerTerm, innerTerms) = appToList (Term (App term1 term2) termDat)
        in case termValue (outerTerm) of 
          Global str -> if str == changedFuncInfoName finfo then 
                          let newInnerTerms = insertHoleToRecCalls ("hole_") innerTerms (changedFuncInfoInds finfo) 
                          in Replace (listToApp (outerTerm, newInnerTerms)) 
                        else 
                          Continue
          term -> Continue
    addHolesToFuncCalls finfo term = Continue   
    --use of function: add holes
    insertHoleToRecCalls :: String -> [Term] -> [Int] -> [Term]
    insertHoleToRecCalls holeNamePrefix termList [] = termList
    insertHoleToRecCalls holeNamePrefix termList (i:is) = 
       let  (l, r) = splitAt i termList 
            stringPrefix = if r==[] then removeSpaces (show (last l)) else removeSpaces (show (head r))
            newVar = Var (holeNamePrefix ++ stringPrefix ++ show i ) 0  
            addedOne = l ++ (genTerm (Hole newVar)):r
            in insertHoleToRecCalls holeNamePrefix addedOne [ j+1 | j <- is]
    --use of constructor: add holes
    addHolesToCtorCalls:: [ChangedCtorInfo] -> Term -> MapResult Term
    addHolesToCtorCalls cinfo (Term (App term1 term2) termDat) = Continue --todo wip
    addHolesToCtorCalls cinfo  term = Continue

-- stack run -- -r examples/testAddIndex.fluid -n add-index2 -a 'data=Data1, type =`List Nat`, index=1'


