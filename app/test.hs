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



replaceOldVar_indices:: [Var] -> Var -> [(Var, Type)] -> [(Var, Type)]
replaceOldVar_indices oldVars newVar [] = []
replaceOldVar_indices oldVars newVar ((var,ty):args) = 
    if elem var oldVars then 
        (newVar,ty):(replaceOldVar_indices oldVars newVar args)
    else 
        (var,ty):(replaceOldVar_indices oldVars newVar args)


checkType:: [(Var, Type)] -> [Int] -> Type -> Bool
checkType argList indPosns ty = all (\i-> snd (argList !! i) == ty ) indPosns


unifyIndices_argsList:: [(Var, Type)] -> [Int] -> [(Var, Type)]
unifyIndices_argsList argList [] = argList
unifyIndices_argsList argList (i:indPosns) = 
    case argList !! i of 
        (var,ty) -> if checkType argList indPosns ty then --check that the indices we want to unify are of the same type
                        --[argList!!j | j <- [0..(length argList)-1] , not (elem j indPosns)]  --remove redundant vars 
                        let oldVars = [fst (argList!!j) | j <- indPosns] in
                            replaceOldVar_indices oldVars var argList
                    else 
                        argList

replaceOldVar_type:: [Var] -> Var -> Type -> Type
replaceOldVar_type oldVars newVar (App t1 t2) = 
    App (replaceOldVar_type oldVars newVar t1) (replaceOldVar_type oldVars newVar t2)
replaceOldVar_type oldVars newVar (V var) = 
    if elem var oldVars then 
        V newVar
    else 
        V var
replaceOldVar_type oldVars newVar ty = ty 


--rename unused var names with the unified one
unifyIndices_retTy:: [(Var, Type)] -> [Int] -> Type -> Type
unifyIndices_retTy argList [] retTy = retTy
unifyIndices_retTy argList (i:indPosns) retTy =   
    case argList !! i of 
        (var,ty) -> let oldVars = [fst (argList!!j) | j <- indPosns] in
                        replaceOldVar_type oldVars var retTy


--recurse to the indices and return type
unifyIndices_constr:: [Int] -> CtorItem -> CtorItem
unifyIndices_constr indPosns (CtorItem itemName ty dataName) = 
    case piTypeToList ty of 
        (argList, retTy) -> let l = length argList   
                                indPosnsRev = map (\i -> l-i) indPosns in 
                                if all (\x -> x<l) indPosnsRev then  -- indices positions valid
                                    let refactoredArgList = unifyIndices_argsList argList indPosnsRev  --refactor indices
                                        refactoredRetType = unifyIndices_retTy argList indPosnsRev retTy in --refactor return type
                                        (CtorItem itemName (listToPiType (refactoredArgList, refactoredRetType)) dataName) 
                                else  --some indices out of bounds
                                    (CtorItem itemName ty dataName)
            



--recurse to the constructor
unifyIndices_data ::  String -> String -> [Int] -> DataItem -> DataItem
unifyIndices_data datName constrName indPosns (DataItem dname dty dConstrs) 
    = DataItem dname 
               dty
               (map (\constr -> if ctorItemName constr == constrName then 
                                    unifyIndices_constr indPosns constr
                                else 
                                    constr
                    ) 
                    dConstrs
                ) 


--recurse to the data type declaration
unifyIndices_ast :: String -> String -> [Int] ->  Program ->  Program
unifyIndices_ast datName constrName indPosns (Program itemL)= 
    Program 
        (map (\item -> 
            case item of 
                (Decl decl) -> Decl decl
                (Data dat) -> if dataName dat == datName then   
                                Data (unifyIndices_data datName constrName indPosns dat)
                              else 
                                Data dat        
            )
            itemL
        )

---------------------------------------------------



updateUsecase_term:: String -> [Int] -> Pat -> Pat
updateUsecase_term constrName indPosns (App t1 t2) = --TODO: recurse down if and case expressions
    let termList = appTermToList (App t1 t2) in 
        case last termList of 
            Global varName -> if varName == constrName then 
                                listToAppTerm (updateUsecase_constrTerm termList indPosns)
                              else 
                                (App t1 t2)
updateUsecase_term constrName indPosns term = term



--change nested App term to (reversed) list
appTermToList:: Term -> [Term]
appTermToList (App t1 t2) = t2:(appTermToList t1) 
appTermToList term = [term]

listToAppTerm:: [Term] -> Term
listToAppTerm [term] = term 
listToAppTerm (term:terms) = App (listToAppTerm terms) term 



--unify var use in term list
unifyVars_termList:: [Term] -> [Int] -> [Term]
unifyVars_termList termList indPosn = 
    map (\i -> if elem (i+1) indPosn then
                    case termList!!i of 
                        V var ->  termList !! ((indPosn!!0)-1) 
                        term -> term 
               else 
                    termList!!i            
        )
        [0..((length termList)-1)]


removeWildcards :: [Term] -> [Term]
removeWildcards termList = termList --TODO: add vars name if wildcards are used


updateUsecase_constrTerm:: [Term] -> [Int] -> [Term]
updateUsecase_constrTerm termList indPosns = 
    let cleanTermList = removeWildcards termList in 
        unifyVars_termList cleanTermList indPosns



updateUsecase_pat:: String -> [Int] -> Pat -> Pat
updateUsecase_pat constrName indPosns (App t1 t2) =
    let termList = appTermToList (App t1 t2) in 
        case last termList of 
            Global varName -> if varName == constrName then 
                                listToAppTerm (updateUsecase_constrTerm termList indPosns)
                              else 
                                (App t1 t2)
updateUsecase_pat constrName indPosns term = term


updateUsecase_pats:: String -> [Int] -> [Pat] -> [Pat]
updateUsecase_pats constrName indPosns [] = []
updateUsecase_pats constrName indPosns (pat:pats) = 
    (updateUsecase_pat constrName indPosns pat):(updateUsecase_pats constrName indPosns pats)


updateUsecase_cl:: String -> [Int] -> Clause -> Clause
updateUsecase_cl constrName indPosns (Clause pats term) = 
    Clause (updateUsecase_pats constrName indPosns pats) (updateUsecase_term constrName indPosns term) 
updateUsecase_cl constrName indPosns (ImpossibleClause pats) = 
    ImpossibleClause (updateUsecase_pats constrName indPosns pats) 


updateUsecase_cls:: String -> [Int] -> [Clause] -> [Clause] 
updateUsecase_cls constrName indPosns [] = []
updateUsecase_cls constrName indPosns (cl:cls) = 
    (updateUsecase_cl constrName indPosns cl):(updateUsecase_cls constrName indPosns cls)


updateUsecase_decl:: String -> String -> [Int] -> DeclItem -> DeclItem
updateUsecase_decl datName constrName indPosns decl = 
    DeclItem (declName decl)
             (declTy decl) 
             (updateUsecase_cls constrName indPosns (declClauses decl) )


updateUsecase :: String -> String -> [Int] ->  Program ->  Program
updateUsecase datName constrName indPosns (Program itemL) = 
    Program 
    (map (\item -> 
            case item of 
                (Decl decl) -> Decl (updateUsecase_decl datName constrName indPosns decl) --only look at uses of constructors in clauses (if used in declaration, should propagate from update use case in data items)
                (Data dat) -> item   -- TODO: not yet implemented - update use case in other data type           
        )
        itemL
    )
    

---------------------------------------------------



--given data name, and constructor name, positions I of the index to unify (index from 0, right to left), 
--all variables in I\I1 will now have the name of I1
--TODO: move the biggest number in I to the front so that we retain the earliest var
tryRefactor:: String ->  String -> String -> [Int] -> Program 
tryRefactor codeStr datName constrName indPosns =  
    let ast = getAST testFileName codeStr in 
        let dataRefactored = unifyIndices_ast datName constrName indPosns ast in 
            updateUsecase datName constrName indPosns dataRefactored
            




showAll :: IO ()
showAll = do
  putStrLn ""
 -- print testData
  putStrLn "original code:"
  fluidCode <- readFile testFileName
  putStrLn fluidCode
  putStrLn "refactored code:"
 -- print (tryRefactor fluidCode "Data1" "C1" [5,4])  
  print (tryRefactor fluidCode "Data2" "C21" [3,2,1])  
  putStrLn ""





    



