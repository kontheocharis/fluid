module Examples.Test (showAll) where

import Checking.Typechecking (checkTerm)
import Parsing.Parser (parseProgram)
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
    Type,
    Var (..),
    piTypeToList,
    listToPiType
  )



testFileName :: String
testFileName = "../app/Examples/test.fluid"

getAST :: String -> String -> Program 
getAST fname fContents = case parseProgram fname fContents of 
                            Left errStr -> Program [] --failed
                            Right prog -> prog


--------------------------


data RefactorArgKind = Name String | Num Int | TermTy Term | Ast Program  deriving (Show)
newtype RefactorArgs = RefactorArgs [(String, RefactorArgKind)] deriving (Show)


--------------------------

--TODO: factor these functions out
--change nested App term to (reversed) list
appTermToList:: Term -> [Term]
appTermToList (App t1 t2) = t2:(appTermToList t1) 
appTermToList term = [term]
--change list to App term
listToAppTerm:: [Term] -> Term
listToAppTerm [term] = term 
listToAppTerm (term:terms) = App (listToAppTerm terms) term 

--------------------------

--add a variable as index to a type use
addIndex_ty :: Var -> Int -> (Var, Type) -> (Var, Type) 
addIndex_ty indVar indPosn (var,ty) = 
    let appList = appTermToList ty 
        (splitL, splitR) = splitAt ((length appList)- indPosn-1) appList in  
        (var, listToAppTerm (splitL ++ [V indVar] ++ splitR))


-- see if data is used as param for constructor, if so, add another param and use it as index
addIndex_ctorParam :: String -> Type -> Int -> [(Var, Type)] -> [(Var, Type)] 
addIndex_ctorParam datName indexTy indPosn [] = []
addIndex_ctorParam datName indexTy indPosn (param:params) = 
    case snd param of 
        Global str -> if str == datName then 
                        let newVar = Var ("ind_for_" ++ (show (fst param))) 0 in 
                            ((newVar,indexTy):((addIndex_ty newVar indPosn param):(addIndex_ctorParam datName indexTy indPosn params)))
                            --todo replace param with one with extra index of given name
                      else 
                        (param:(addIndex_ctorParam datName indexTy indPosn params))
        ty -> (param:(addIndex_ctorParam datName indexTy indPosn params))




--add index to the use of data
addIndex_tyUse:: String -> Var -> Int -> Type -> Type 
addIndex_tyUse datName newVar indPosn term = 
    let appList = appTermToList term 
        (splitL, splitR) = splitAt ((length appList)- indPosn-1) appList in 
        listToAppTerm (splitL ++ [V newVar] ++ splitR)



addIndex_ctor:: String -> Type -> Int -> CtorItem -> CtorItem
addIndex_ctor datName indexTy indPosn (CtorItem cname cty dname) = 
    let (tyList, retTy) = piTypeToList cty  
        newVar = Var ("ind_for_" ++ datName ++ "_" ++ cname ) 0  --TODO: need better naming system
        newRetTy = addIndex_tyUse datName newVar indPosn retTy           --update the return type of each data
        newParams = addIndex_ctorParam datName indexTy indPosn tyList in  --update its use as params to constructor (TODO: not used for now)
        (CtorItem cname 
                  (listToPiType (tyList ++ [(newVar, indexTy)], newRetTy) )  --also need to add an additional param for the index of ret ty 
                  dname)


--add index at a given position to the signature (a pi type) 
addInd_sig:: String -> Type -> Int -> Type -> Type 
addInd_sig datName indexTy indPosn ty = 
    let (tyList, retTy) = piTypeToList ty 
        (splitL, splitR) = splitAt indPosn tyList 
        newVarName = "index_" ++  "_"  ++  (show (length tyList)) ++  "_"  ++ (show indPosn)  in 
        listToPiType ((splitL ++ [((Var newVarName (0)) , indexTy)] ++ splitR), retTy) --TODO: how to get fresh variables?



addIndex_data:: String ->  Type -> Int -> DataItem -> DataItem
addIndex_data datName indexTy indPosn (DataItem name ty ctors) = 
    (DataItem name 
              (addInd_sig datName indexTy indPosn ty)   --add index to the signature of data declaration 
              (map (addIndex_ctor datName indexTy indPosn) 
                    ctors )) 
--todo: (addInd_ty indexTy indPosn ctors)


addIndex_ast:: String -> Type -> Int -> Program ->  Program
addIndex_ast datName indexTy indPosn (Program items) = 
    Program
        (map (\item -> 
            case item of 
                (Decl decl) -> Decl decl
                (Data dat) -> if dataName dat == datName then   
                                Data (addIndex_data datName indexTy indPosn dat)
                              else 
                                Data dat            
            )
            items
    )
    -- update use sites in functions and other data definition?
    --todo: trigger refactoring of adding index to functions, and update _their_ usesites 


--------------------------





--add params to funct and use as index of another param
--addParamsToFunc


--TODO: add to refactoring queue: update usecase of function elsewhere 




--------------------------

--NOTE: Assume that the extra param in ctors are always at the end...



insertAt_appterm::  Int ->  Term -> Term  -> Term
insertAt_appterm indPosn newTerm appTerm = 
    let appList = appTermToList appTerm 
        (l,r) = splitAt ((length appList)- indPosn-1) appList in    
        (listToAppTerm (l ++ [newTerm] ++ r))


useVarAsInd::  Int ->  Var -> (Var,Type) -> (Var,Type)  
useVarAsInd indPosn var (v,ty) = 
    (v, insertAt_appterm indPosn (V var) ty )



--
insertAtAndRelate_sig::  Int -> [(Var, Type)] -> [(Int, (Var, Type))] -> [(Var, Type)]  --todo: factor out insertAt operation
insertAtAndRelate_sig indPosn list [] = list
insertAtAndRelate_sig indPosn list ((i,elt):res) = 
    let (l,r) = splitAt (i+1) list       
        addedOne = [l!!k | k<-[0..(length l -2)]] 
                    ++ ([(useVarAsInd indPosn (fst elt) (last l))   ]) 
                    ++ [elt] ++ r  in 
        insertAtAndRelate_sig indPosn addedOne [(j+1, e) | (j,e) <- res ]
        



isMyData:: Type -> String -> Bool 
isMyData ty name =  case ty of  
                        Global str -> if str == name then 
                                            True
                                        else 
                                            False 
                        term -> False 



--todo: factor this out
sigListToPiTy:: [(Var, Type)] ->  Type 
sigListToPiTy [] = listToPiType ([], TyT) --should not happen 
sigListToPiTy ((v,t):l) = listToPiType ((reverse l), t)





tryInsert_appTerm:: Term -> Term -> Term
tryInsert_appTerm newTerm appTerm = 
    let appList = appTermToList appTerm in  
        case last appList  of 
            Global str -> (listToAppTerm ([newTerm] ++ appList)) --if pattern is a constructor, add to the end
            term -> appTerm          --otherwise (is a variable or Wild),  do not need to add anything                             
--note: assume that the new index is added as the last param of each constructor



insertAtAndRelate_terms:: [Term] ->  [(Int,Term)] -> [Term]
insertAtAndRelate_terms list [] = list
insertAtAndRelate_terms list ((i,elt):res) = 
    let (l,r) = splitAt (i+1) list   in 
        case r of 
            [] -> l ++ [elt]
            (rfst:rres) -> let addedOne = l ++ [elt] ++ [tryInsert_appTerm elt rfst]
                                         ++ rres in    
                                insertAtAndRelate_terms addedOne [(j+1, e) | (j,e) <- res ]


insertAt_terms:: [Term] ->  [(Int,Term)] -> [Term]
insertAt_terms list [] = list
insertAt_terms list ((i,elt):res) = 
    let (l,r) = splitAt (i+1) list  
        addedOne = l ++ [elt] ++ r in    
        insertAt_terms addedOne [(j+1, e) | (j,e) <- res ]



--adds new variable in appropriate sites 
updataUsecaseInFunc_clLHS:: String -> Int -> [Int] -> [Pat] -> [Pat]  
updataUsecaseInFunc_clLHS  datName indPosn dataPosns pats = 
    insertAtAndRelate_terms pats [(i, V (Var ("patVar_" ++ (show i)) 0)) | i <-dataPosns ]


addHolestoAppList:: [Term] -> [Int] -> [Term] 
addHolestoAppList appList dataPosns = insertAt_terms appList [ (i-1, (Hole (Var ("holeForNewParam_" ++ (show i)) 0))) |i<-dataPosns ]

--update recursive calls only 
--note: use of constructors in rhs not updated here (will do later)
updataUsecaseInFunc_clRHS:: String -> String -> Int -> [Int] -> Term -> Term  
updataUsecaseInFunc_clRHS funcName datName indPosn dataPosns (App term1 term2) = 
    let appList  = appTermToList (App term1 term2) 
        defRes = (App (updataUsecaseInFunc_clRHS funcName datName indPosn dataPosns term1) 
                      (updataUsecaseInFunc_clRHS funcName datName indPosn dataPosns term2))      in 
        case last appList of 
            Global str -> if str == funcName then 
                            listToAppTerm (addHolestoAppList appList dataPosns)
                          else 
                            defRes
            term -> defRes          
updataUsecaseInFunc_clRHS funcName datName indPosn dataPosns term = term      
--TODO: recurse down other structures


--update function clauses  --
updataUsecaseInFunc_cl::  String ->  String -> Int -> [Int] -> Clause -> Clause  
updataUsecaseInFunc_cl funcName datName indPosn dataPosns (Clause lhs rhs) = 
    (Clause (updataUsecaseInFunc_clLHS datName indPosn dataPosns lhs)  
            (updataUsecaseInFunc_clRHS funcName datName indPosn dataPosns rhs )) --todo: refactor rhs, needs 
updataUsecaseInFunc_cl funcName datName indPosn dataPosns (ImpossibleClause lhs) = 
    (ImpossibleClause (updataUsecaseInFunc_clLHS datName indPosn dataPosns lhs))  



--note: inefficient but works
updataUsecaseInFunc_decl :: String -> Type -> Int -> DeclItem ->  [(String, RefactorArgs)] ->  (DeclItem, [(String, RefactorArgs)])  
updataUsecaseInFunc_decl datName indexTy indPosn (DeclItem funcName typ clauses) q = 
    let (inpTys, resTy) = piTypeToList typ 
        sig = inpTys ++ [((Var "dummyVar" 0) , resTy)] 
        revSig = reverse  sig 
        dataPosns = filter (\j-> isMyData (snd (revSig !!j)) datName ) 
                            [0..(length revSig)-1]   
        newSig =  insertAtAndRelate_sig indPosn revSig  
                                        [(j, ((Var ("paramForInd_" ++ (show j)) 0), indexTy) ) | j <- dataPosns]  in 
            (DeclItem funcName 
                      (sigListToPiTy newSig) 
                      (map (updataUsecaseInFunc_cl funcName datName indPosn dataPosns) clauses),
             [])  
--TODO: update queue to also updates of usecase of f elsewhere (not needed for paper - eval is not used in other functions)


updataUsecaseInFunc_item :: String -> Type -> Int -> Item ->  [(String, RefactorArgs)] ->  (Item, [(String, RefactorArgs)])  
updataUsecaseInFunc_item datName indexTy indPosn (Data dat) q = ((Data dat), q)
updataUsecaseInFunc_item datName indexTy indPosn (Decl decl) q = 
    let (refdDecl, newQ) = updataUsecaseInFunc_decl datName indexTy indPosn decl q in 
        (Decl refdDecl, newQ ++ q)


updataUsecaseInFunc_items :: String -> Type -> Int -> [Item] ->  [(String, RefactorArgs)] ->  ([Item], [(String, RefactorArgs)])  
updataUsecaseInFunc_items datName indexTy indPosn [] q = ([], q)
updataUsecaseInFunc_items datName indexTy indPosn (item:items) q = 
    let (recItems, recQ) = updataUsecaseInFunc_items datName indexTy indPosn items q 
        (refactoredItem, refQ) = updataUsecaseInFunc_item datName indexTy indPosn item q in 
        ((refactoredItem:recItems), refQ ++ recQ ++ q )



updataUsecaseInFunc_ast :: String -> Type -> Int -> Program ->  (Program, [(String, RefactorArgs)])  
updataUsecaseInFunc_ast datName indexTy indPosn (Program items) = 
    let (newItems, q) = updataUsecaseInFunc_items datName indexTy indPosn items [] in 
        (Program (newItems), q)


--------------------------

updateUsecaseInCtor_ast:: String -> Type -> Int -> Program ->  Program
updateUsecaseInCtor_ast datName indexTy indPosn (Program items) = Program (items) --WIP
   -- let (newItems, q) = updataUsecaseInFunc_items datName indexTy indPosn items [] in 
   --     (Program (newItems), q)


--------------------------

updateQueuedUsecase_ast :: String -> Type -> Int -> Program -> [(String, RefactorArgs)] -> (Program, [(String, RefactorArgs)]) 
updateQueuedUsecase_ast datName indexTy indPosn ast [] = (ast, [])
updateQueuedUsecase_ast datName indexTy indPosn ast (refact:queue) = 
    if (fst refact)  == "useInFunc" then   
        let (refacted, newQ) = updataUsecaseInFunc_ast datName indexTy indPosn ast in --todo: use argument list
            updateQueuedUsecase_ast datName indexTy indPosn refacted (newQ ++ queue)
    else if (fst refact)  == "useInCurrCtor" then   
        let refacted = updateUsecaseInCtor_ast datName indexTy indPosn ast in --todo: use argument list
            updateQueuedUsecase_ast datName indexTy indPosn refacted queue
    else --TODO: implement other refactoring   --other triggered refactoring should take in String that represents the arguments
        updateQueuedUsecase_ast datName indexTy indPosn ast  queue
--e.g. if f is a function that uses Data1, then we would have added params to f, then any call of f elsewhere would need to be updates


--------------------------

--given data name, and index type to add, position of new index
--adds index before the current i position (right to left, from 0)
tryRefactor:: String ->  String -> Type -> Int -> Program
tryRefactor codeStr datName indexTy indPosn =  
    let ast = getAST testFileName codeStr in 
        if indPosn <0 then  
            ast
        else 
            let updatedData = addIndex_ast datName indexTy indPosn ast in         
                fst (updateQueuedUsecase_ast datName indexTy indPosn updatedData 
                                             [("useInFunc", RefactorArgs []), ("useInCurrCtor", RefactorArgs [])])  --todo use arg list
                --["useInFunc","useInCurrCtor","useAsIndex","useInOtherCtor"])



--todo: store possible refactoring namews in a data, instead of using string.



showAll :: IO ()
showAll = do
  putStrLn ""
 -- print testData
  putStrLn "original code:"
  fluidCode <- readFile testFileName
  putStrLn fluidCode
  putStrLn "refactored code:"
  print  (tryRefactor fluidCode "Data1" (ListT NatT) 1)  
  putStrLn ""




--TODO: possibly need a refactoring to reorder params