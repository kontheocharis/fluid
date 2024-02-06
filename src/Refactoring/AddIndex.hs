module Refactoring.AddIndex (addIndex) where

import Data.List (findIndices)
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
    piTypeToList, genTerm
  )
import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupExprArg, lookupIdxArg, lookupNameArg)

--------------------------

-- TODO: factor these functions out
-- change nested App term to (reversed) list
appTermToList :: Term -> [Term]
appTermToList (Term (App t1 t2) _) = t2 : (appTermToList t1)
appTermToList term = [term]

-- change list to App term
listToAppTerm :: [Term] -> Term
listToAppTerm [term] = term
listToAppTerm (term : terms) = genTerm (App (listToAppTerm terms) term)

--------------------------

-- add a variable as index to a type use
addIndex_ty :: Var -> Int -> (Var, Type) -> (Var, Type)
addIndex_ty indVar indPosn (var, ty) =
  let appList = appTermToList ty
      (splitL, splitR) = splitAt ((length appList) - indPosn - 1) appList
   in (var, listToAppTerm (splitL ++ [genTerm (V indVar)] ++ splitR))

-- see if data is used as param for constructor, if so, add another param and use it as index
addIndex_ctorParam :: String -> Type -> Int -> [(Var, Type)] -> [(Var, Type)]
addIndex_ctorParam datName indexTy indPosn [] = []
addIndex_ctorParam datName indexTy indPosn (param : params) =
  case termValue (snd param) of
    Global str ->
      if str == datName
        then
          let newVar = Var ("ind_for_" ++ (show (fst param))) 0
           in ((newVar, indexTy) : ((addIndex_ty newVar indPosn param) : (addIndex_ctorParam datName indexTy indPosn params)))
        else -- todo replace param with one with extra index of given name

          (param : (addIndex_ctorParam datName indexTy indPosn params))
    ty -> (param : (addIndex_ctorParam datName indexTy indPosn params))

-- add index to the use of data
addIndex_tyUse :: String -> Var -> Int -> Type -> Type
addIndex_tyUse datName newVar indPosn term =
  let appList = appTermToList term
      (splitL, splitR) = splitAt ((length appList) - indPosn - 1) appList
   in listToAppTerm (splitL ++ (genTerm (V newVar)):splitR)

addIndex_ctor :: String -> Type -> Int -> CtorItem -> CtorItem
addIndex_ctor datName indexTy indPosn (CtorItem cname cty dname) =
  let (tyList, retTy) = piTypeToList cty
      newVar = Var ("ind_for_" ++ datName ++ "_" ++ cname) 0 -- TODO: need better naming system
      newRetTy = addIndex_tyUse datName newVar indPosn retTy -- update the return type of each data
      newParams = addIndex_ctorParam datName indexTy indPosn tyList -- update its use as params to constructor (TODO: not used for now)
   in ( CtorItem
          cname
          (listToPiType (tyList ++ [(newVar, indexTy)], newRetTy)) -- also need to add an additional param for the index of ret ty
          dname
      )

-- add index at a given position to the signature (a pi type)
addInd_sig :: String -> Type -> Int -> Type -> Type
addInd_sig datName indexTy indPosn ty =
  let (tyList, retTy) = piTypeToList ty
      (splitL, splitR) = splitAt indPosn tyList
      newVarName = "index_" ++ "_" ++ (show (length tyList)) ++ "_" ++ (show indPosn)
   in listToPiType ((splitL ++ [((Var newVarName (0)), indexTy)] ++ splitR), retTy) -- TODO: how to get fresh variables?

addIndex_data :: String -> Type -> Int -> DataItem -> DataItem
addIndex_data datName indexTy indPosn (DataItem name ty ctors) =
  ( DataItem
      name
      (addInd_sig datName indexTy indPosn ty) -- add index to the signature of data declaration
      ( map
          (addIndex_ctor datName indexTy indPosn)
          ctors
      )
  )

-- todo: (addInd_ty indexTy indPosn ctors)

addIndex_ast :: String -> Type -> Int -> Program -> Program
addIndex_ast datName indexTy indPosn (Program items) =
  Program
    ( map
        ( \item ->
            case item of
              (Decl decl) -> Decl decl
              (Data dat) ->
                if dataName dat == datName
                  then Data (addIndex_data datName indexTy indPosn dat)
                  else Data dat
        )
        items
    )

-- update use sites in functions and other data definition?
-- todo: trigger refactoring of adding index to functions, and update _their_ usesites

--------------------------

-- TODO: add to refactoring queue: update usecase of function elsewhere

-- TODO: update of pattern variable assumes that all param has a pattern v, but it's not a safe assumption
--------------------------

-- NOTE: Assume that the extra param in ctors are always at the end...
insertAt_appterm :: Int -> Term -> Term -> Term
insertAt_appterm indPosn newTerm appTerm =
  let appList = appTermToList appTerm
      (l, r) = splitAt ((length appList) - indPosn - 1) appList
   in (listToAppTerm (l ++ [newTerm] ++ r))

useVarAsInd :: Int -> Var -> (Var, Type) -> (Var, Type)
useVarAsInd indPosn var (v, ty) =
  (v, insertAt_appterm indPosn (genTerm (V var)) ty)

--
insertAtAndRelate_sig :: Int -> [(Var, Type)] -> [(Int, (Var, Type))] -> [(Var, Type)] -- todo: factor out insertAt operation
insertAtAndRelate_sig indPosn list [] = list
insertAtAndRelate_sig indPosn list ((i, elt) : res) =
  let (l, r) = splitAt (i + 1) list
      addedOne =
        (take ((length l) - 1) l)
          ++ ([(useVarAsInd indPosn (fst elt) (last l))])
          ++ [elt]
          ++ r
   in insertAtAndRelate_sig indPosn addedOne [(j + 1, e) | (j, e) <- res]

isMyData :: Type -> String -> Bool
isMyData ty name = case termValue ty of
  Global str ->
    if str == name
      then True
      else False
  term -> False

-- todo: factor this out
sigListToPiTy :: [(Var, Type)] -> Type
sigListToPiTy [] = listToPiType ([], genTerm TyT) -- should not happen
sigListToPiTy ((v, t) : l) = listToPiType ((reverse l), t)

tryInsert_appTerm :: Term -> Term -> Term
tryInsert_appTerm newTerm appTerm =
  let appList = appTermToList appTerm
   in case termValue (last appList) of
        Global str -> (listToAppTerm (newTerm : appList)) -- if pattern is a constructor, add to the end
        term -> appTerm -- otherwise (is a variable or Wild),  do not need to add anything
        -- note: assume that the new index is added as the last param of each constructor

insertAtAndRelate_terms :: [Term] -> [(Int, Term)] -> [Term]
insertAtAndRelate_terms list [] = list
insertAtAndRelate_terms list ((i, elt) : res) =
  let (l, r) = splitAt (i + 1) list
   in case r of
        [] -> l ++ [elt]
        (rfst : rres) ->
          let addedOne =
                l
                  ++ [elt]
                  ++ [tryInsert_appTerm elt rfst]
                  ++ rres
           in insertAtAndRelate_terms addedOne [(j + 1, e) | (j, e) <- res]

insertAt_terms :: [Term] -> [(Int, Term)] -> [Term]
insertAt_terms list [] = list
insertAt_terms list ((i, elt) : res) =
  let (l, r) = splitAt (i + 1) list
      addedOne = l ++ [elt] ++ r
   in insertAt_terms addedOne [(j + 1, e) | (j, e) <- res]

-- adds new variable in appropriate sites
updataUsecaseInFunc_clLHS :: Int -> [Int] -> [Pat] -> [Pat]
updataUsecaseInFunc_clLHS indPosn dataPosns pats =
  insertAtAndRelate_terms pats [(i-1, genTerm (V (Var ("patVar_" ++ (show i)) 0))) | i <- dataPosns]

---insertAtAndRelate_terms but relate the correct term
insertAtAndRelate_terms2 :: [Term] -> [(Int, Term)] -> [Term]
insertAtAndRelate_terms2 list [] = list
insertAtAndRelate_terms2 list ((i, elt) : res) =
  let (l, r) = splitAt (i + 1) list
   in case l of
        [] ->
          let addedOne = [elt] ++ r
           in insertAtAndRelate_terms2 addedOne [(j + 1, e) | (j, e) <- res]
        l ->
          let addedOne = (take (length l - 1) l) ++ [tryInsert_appTerm elt (last l)] ++ [elt] ++ r
           in insertAtAndRelate_terms2 addedOne [(j + 1, e) | (j, e) <- res]

-- if the next param is a constructor, then relate the holes
-- Q: can we just leave as differently named holes and run unifier to relate them? (not an issue for paper)

addHolestoAppList :: [Term] -> [Int] -> [Term]
addHolestoAppList appList dataPosns = insertAtAndRelate_terms2 appList [(i - 1, genTerm  (Hole (Var ("holeForNewParam_" ++ (show i)) 0))) | i <- dataPosns]

-- update recursive calls only
-- note: use of constructors in rhs not updated here (will do later)
updataUsecaseInFunc_clRHS :: [String] -> String -> Int -> [Int] -> Term -> Term
updataUsecaseInFunc_clRHS ctorNames funcName indPosn dataPosns (Term (App term1 term2) termDat) =
  let appList = appTermToList (Term (App term1 term2) termDat)
      defRes =
        genTerm ( App
            (updataUsecaseInFunc_clRHS ctorNames funcName indPosn dataPosns term1)
            (updataUsecaseInFunc_clRHS ctorNames funcName indPosn dataPosns term2)
        )
   in case termValue (last appList) of
        Global str ->
          if (elem str ctorNames)
            then listToAppTerm (genTerm (Hole (Var ("holeForConstUse_" ++ str) 0)) : appList)
            else
              if str == funcName -- if recursive call, add holes for args, and relate
                then
                  let addedHoles = (addHolestoAppList appList dataPosns)
                   in listToAppTerm addedHoles
                else defRes
        term -> defRes
updataUsecaseInFunc_clRHS ctorNames funcName indPosn dataPosns (Term (Case cTerm ptList) termDat) 
  = genTerm (Case (updataUsecaseInFunc_clRHS  ctorNames funcName indPosn dataPosns cTerm)
                  (map (\pt -> ((updataUsecaseInFunc_clLHS indPosn dataPosns [(fst pt)])!!0 ,  updataUsecaseInFunc_clRHS ctorNames funcName indPosn dataPosns (snd pt)) ) ptList))
updataUsecaseInFunc_clRHS ctorNames funcName indPosn dataPosns term = term

-- TODO: recurse down other structures

-- update function clauses  --
updataUsecaseInFunc_cl :: [String] -> String -> Int -> [Int] -> Clause -> Clause
updataUsecaseInFunc_cl ctorNames funcName indPosn dataPosns (Clause lhs rhs) =
  ( Clause
      (updataUsecaseInFunc_clLHS indPosn dataPosns lhs)
      (updataUsecaseInFunc_clRHS ctorNames funcName indPosn dataPosns rhs) -- todo: refactor rhs, needs
  )
updataUsecaseInFunc_cl ctorNames funcName indPosn dataPosns (ImpossibleClause lhs) =
  (ImpossibleClause (updataUsecaseInFunc_clLHS indPosn dataPosns lhs))

-- note: inefficient but works
updataUsecaseInFunc_decl :: [String] -> String -> Type -> Int -> DeclItem -> [(String)] -> (DeclItem, [(String)])
updataUsecaseInFunc_decl ctorNames datName indexTy indPosn (DeclItem funcName typ clauses) q =
  let (inpTys, resTy) = piTypeToList typ
      sig = inpTys ++ [((Var "dummyVar" 0), resTy)]
      revSig = reverse sig
      dataPosns =
        filter
          (\j -> isMyData (snd (revSig !! j)) datName)
          [0 .. (length revSig) - 1]
      newSig =
        insertAtAndRelate_sig
          indPosn
          revSig
          [(j, ((Var ("paramForInd_" ++ (show j)) 0), indexTy)) | j <- dataPosns]
   in ( DeclItem
          funcName
          (sigListToPiTy newSig)
          (map (updataUsecaseInFunc_cl ctorNames funcName indPosn dataPosns) clauses),
        []
      )

-- TODO: update queue to also updates of usecase of f elsewhere (not needed for paper - eval is not used in other functions)

updataUsecaseInFunc_item :: [String] -> String -> Type -> Int -> Item -> [(String)] -> (Item, [(String)])
updataUsecaseInFunc_item ctorNames datName indexTy indPosn (Data dat) q = ((Data dat), q)
updataUsecaseInFunc_item ctorNames datName indexTy indPosn (Decl decl) q =
  let (refdDecl, newQ) = updataUsecaseInFunc_decl ctorNames datName indexTy indPosn decl q
   in (Decl refdDecl, newQ ++ q)

updataUsecaseInFunc_items :: [String] -> String -> Type -> Int -> [Item] -> [(String)] -> ([Item], [(String)])
updataUsecaseInFunc_items ctorNames datName indexTy indPosn [] q = ([], q)
updataUsecaseInFunc_items ctorNames datName indexTy indPosn (item : items) q =
  let (recItems, recQ) = updataUsecaseInFunc_items ctorNames datName indexTy indPosn items q
      (refactoredItem, refQ) = updataUsecaseInFunc_item ctorNames datName indexTy indPosn item q
   in ((refactoredItem : recItems), refQ ++ recQ ++ q)

getCtorName :: String -> [Item] -> [String]
getCtorName datName [] = []
getCtorName datName ((Decl decl) : items) = getCtorName datName items
getCtorName datName ((Data dat) : items) =
  if dataName dat == datName
    then (map (\ctorItem -> ctorItemName ctorItem) (dataCtors dat)) ++ getCtorName datName items
    else getCtorName datName items

updataUsecaseInFunc_ast :: String -> Type -> Int -> Program -> (Program, [(String)])
updataUsecaseInFunc_ast datName indexTy indPosn (Program items) =
  let ctorNames = getCtorName datName items
      (newItems, q) = updataUsecaseInFunc_items ctorNames datName indexTy indPosn items []
   in (Program (newItems), q)

---TODO: future: gather where to add new params in ctor instead of going through ast twice

--------------------------

insertAtAndRelate_sig2 :: Int -> [(Var, Type)] -> [(Int, (Var, Type))] -> [(Var, Type)] -- todo: unify the two insertAtAndRelate_sig
insertAtAndRelate_sig2 indPosn list [] = list
insertAtAndRelate_sig2 indPosn list ((i, elt) : res) =
  let (l, r) = splitAt (i + 1) list
   in case r of
        [] -> l ++ [elt]
        (rfst : rres) ->
          let addedOne =
                l
                  ++ [elt]
                  ++ ([(useVarAsInd indPosn (fst elt) rfst)])
                  ++ rres
           in insertAtAndRelate_sig2 indPosn addedOne [(j + 1, e) | (j, e) <- res]

useInCtor_ctor :: String -> Type -> Int -> (CtorItem, [(String, [Int])]) -> (CtorItem, [(String, [Int])])
useInCtor_ctor datName indexTy indPosn ((CtorItem cName cTy cDatName), list) =
  let (inpTY, resTy) = piTypeToList (cTy)
      dataPosns =
        filter
          (\j -> isMyData (snd (inpTY !! j)) datName)
          [0 .. (length inpTY) - 1]
      newInpTy = insertAtAndRelate_sig2 indPosn inpTY [(j - 1, ((Var ("varForDataUse_" ++ cName ++ "_" ++ (show j)) 0), indexTy)) | j <- dataPosns]
      newCtor =
        ( CtorItem
            cName
            (listToPiType (newInpTy, resTy))
            cDatName
        )
   in (newCtor, ((cName, dataPosns) : list))

useInCtor_ctors :: String -> Type -> Int -> ([CtorItem], [(String, [Int])]) -> ([CtorItem], [(String, [Int])])
useInCtor_ctors datName indexTy indPosn ([], list) = ([], list)
useInCtor_ctors datName indexTy indPosn (((CtorItem cName cTy cDatName) : ctors), list) =
  let (inpTY, resTy) = piTypeToList (cTy)
      dataPosns = filter (\j -> isMyData (snd (inpTY !! j)) datName) [0 .. (length inpTY) - 1]
      newInpTy = insertAtAndRelate_sig2 indPosn inpTY [(j - 1, ((Var ("varForDataUse_" ++ cName ++ "_" ++ (show j)) 0), indexTy)) | j <- dataPosns]
      newCtor =
        ( CtorItem
            cName
            (listToPiType (newInpTy, resTy))
            cDatName
        )
      (recCtors, recList) = useInCtor_ctors datName indexTy indPosn (ctors, list)
   in (newCtor : recCtors, list ++ ((cName, dataPosns) : recList))

updateUsecaseInCtor_items :: String -> Type -> Int -> ([Item], [(String, [Int])]) -> ([Item], [(String, [Int])])
updateUsecaseInCtor_items datName indexTy indPosn ([], list) = ([], list)
updateUsecaseInCtor_items datName indexTy indPosn (((Decl decl) : items), list) =
  let (recItems, recList) = updateUsecaseInCtor_items datName indexTy indPosn (items, list)
   in ((Decl decl) : recItems, recList ++ list)
updateUsecaseInCtor_items datName indexTy indPosn (((Data dat) : items), list) =
  case dat of
    (DataItem dName dTy ctors) ->
      if dName == datName
        then
          let (recItems, recList) = updateUsecaseInCtor_items datName indexTy indPosn (items, list)
              (newCtors, newList) = useInCtor_ctors datName indexTy indPosn (ctors, [])
           in ((Data (DataItem dName dTy newCtors)) : recItems, list ++ newList ++ recList)
        else
          let (recItems, recList) = updateUsecaseInCtor_items datName indexTy indPosn (items, list)
           in ((Data dat) : recItems, recList ++ list)

----------------

addHolesToAppList :: [Term] -> [Int] -> [Term]
addHolesToAppList list inds = insertAt_terms list (map (\i -> (i - 1, genTerm (Hole (Var ("holeForUpdatedCtor_" ++ (show i)) 0)))) inds)

-- todo: assumed constructor params are all present

addPatternVarsOfCtorUse_rhsterm :: String -> Type -> Int -> [(String, [Int])] -> Term -> Term
addPatternVarsOfCtorUse_rhsterm datName indexTy indPosn changedCtors (Term (App term1 term2) termD) =
  let appList = appTermToList (Term (App term1 term2) termD)
   in case termValue (last appList) of
        Global str ->
          let changedCtorPosns = findIndices (\pair -> fst pair == str) changedCtors
           in if length changedCtorPosns > 0
                then listToAppTerm (addHolesToAppList appList (snd (changedCtors !! (changedCtorPosns !! 0))))
                else genTerm (App (addPatternVarsOfCtorUse_rhsterm datName indexTy indPosn changedCtors term1) (addPatternVarsOfCtorUse_rhsterm datName indexTy indPosn changedCtors term2))
        term -> genTerm (App (addPatternVarsOfCtorUse_rhsterm datName indexTy indPosn changedCtors term1) (addPatternVarsOfCtorUse_rhsterm datName indexTy indPosn changedCtors term2))
addPatternVarsOfCtorUse_rhsterm datName indexTy indPosn changedCtors term = term

-- TODO: recurse down case and ifs

addVarToAppList :: [Term] -> [Int] -> [Term]
addVarToAppList list inds = insertAt_terms list (map (\i -> (i +1, genTerm (V (Var ("vForUpdatedCtor_" ++ (show i)) 0)))) inds) -- todo: index correct?

-- todo: for now, assume that data is a param, so do not need to recurse down App
addPatternVarsOfCtorUse_term :: String -> Type -> Int -> [(String, [Int])] -> Pat -> Pat
addPatternVarsOfCtorUse_term datName indexTy indPosn changedCtors (Term (App term1 term2) termD) =
  let appList = appTermToList (Term (App term1 term2) termD)
   in case termValue (last appList) of
        Global str ->
          let changedCtorPosns = findIndices (\pair -> fst pair == str) changedCtors
           in if length changedCtorPosns > 0
                then listToAppTerm (addVarToAppList appList (snd (changedCtors !! (changedCtorPosns !! 0))))
                else Term (App term1 term2) termD -- no change needed
        term -> Term (App term1 term2) termD -- otherwise (is a variable or Wild),  do not need to add anything
addPatternVarsOfCtorUse_term datName indexTy indPosn changedCtors pat = pat

-- TODO: recurse down case and ifs

addPatternVarsOfCtorUse_pats :: String -> Type -> Int -> [(String, [Int])] -> [Pat] -> [Pat]
addPatternVarsOfCtorUse_pats datName indexTy indPosn changedCtors = map (addPatternVarsOfCtorUse_term datName indexTy indPosn changedCtors)

updateCtorUsecase_cl :: String -> Type -> Int -> [(String, [Int])] -> Clause -> Clause
updateCtorUsecase_cl datName indexTy indPosn changedCtors (Clause pats term) =
  (Clause (addPatternVarsOfCtorUse_pats datName indexTy indPosn changedCtors pats) (addPatternVarsOfCtorUse_rhsterm datName indexTy indPosn changedCtors term))
updateCtorUsecase_cl datName indexTy indPosn changedCtors (ImpossibleClause pats) =
  (ImpossibleClause (addPatternVarsOfCtorUse_pats datName indexTy indPosn changedCtors pats))

-- if ctors used in lhs, then add a var, if on rhs, add a hole
updateCtorUsecase_decl :: String -> Type -> Int -> [(String, [Int])] -> DeclItem -> DeclItem
updateCtorUsecase_decl datName indexTy indPosn changedCtors (DeclItem dname dty dcl) =
  DeclItem dname dty (map (updateCtorUsecase_cl datName indexTy indPosn changedCtors) dcl)

updateCtorUsecase_items :: String -> Type -> Int -> [(String, [Int])] -> [Item] -> [Item]
updateCtorUsecase_items datName indexTy indPosn changedCtors [] = []
updateCtorUsecase_items datName indexTy indPosn changedCtors ((Data dat) : items) =
  ((Data dat) : (updateCtorUsecase_items datName indexTy indPosn changedCtors items)) -- todo: not implemented, use of updated ctos in other data
updateCtorUsecase_items datName indexTy indPosn changedCtors ((Decl decl) : items) =
  -- todo: check datName not used in function, move on
  ((Decl (updateCtorUsecase_decl datName indexTy indPosn changedCtors decl)) : (updateCtorUsecase_items datName indexTy indPosn changedCtors items))

-- todo: for now, only change if datName used as a direct param of function (not as index of params)

updateUsecaseInCtor_ast :: String -> Type -> Int -> Program -> Program
updateUsecaseInCtor_ast datName indexTy indPosn (Program items) =
  let (newItems, changedCtors) = updateUsecaseInCtor_items datName indexTy indPosn (items, []) -- update use of data in ctors
   in Program (updateCtorUsecase_items datName indexTy indPosn changedCtors newItems) -- update use of Ctor in other functions


--------------------------




updateQueuedUsecase_ast :: String -> Type -> Int -> Program -> [(String)] -> (Program, [(String)])
updateQueuedUsecase_ast datName indexTy indPosn ast [] = (ast, [])
updateQueuedUsecase_ast datName indexTy indPosn ast (refact : queue) =
  if (refact) == "useInFunc"
    then
      let (refacted, newQ) = updataUsecaseInFunc_ast datName indexTy indPosn ast -- todo: use argument list
       in updateQueuedUsecase_ast datName indexTy indPosn refacted (newQ ++ queue)
    else
      if (refact) == "useInCurrCtor"
        then
          let refacted = updateUsecaseInCtor_ast datName indexTy indPosn ast -- todo: use argument list
           in updateQueuedUsecase_ast datName indexTy indPosn refacted queue
        else -- TODO: implement other refactoring   --other triggered refactoring should take in String that represents the arguments
          updateQueuedUsecase_ast datName indexTy indPosn ast queue

-- e.g. if f is a function that uses Data1, then we would have added params to f, then any call of f elsewhere would need to be updated (not implemented)

--------------------------



data AddIndexArgs = AddIndexArgs
  { -- | The name of the data type to specialise.
    addIndDataName :: String,
    -- | The type of the new index
    addIndIndexType :: Term,
    -- | The position  of the new index
    addIndIndexPos :: Int

  }

instance FromRefactorArgs AddIndexArgs where
  fromRefactorArgs args =
    AddIndexArgs
      <$> lookupNameArg "data" args
      <*> lookupExprArg "type" args
      <*> lookupIdxArg "index" args
     



addIndex :: AddIndexArgs -> Program -> Refact Program
addIndex args ast =
  let updatedData = addIndex_ast (addIndDataName args) (addIndIndexType args) (addIndIndexPos args) ast 
    in return (fst
                ( updateQueuedUsecase_ast
                    (addIndDataName args)
                    (addIndIndexType args)
                    (addIndIndexPos args)
                    updatedData
                    [("useInFunc"), ("useInCurrCtor")] -- todo use arg list
                ))



-- stack run -- -r examples/testAddIndex.fluid -n add-index -a 'data=Data1, type =`List Nat`, index=1'

