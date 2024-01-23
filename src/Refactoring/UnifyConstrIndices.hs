module Refactoring.UnifyConstrIndices (unifyIndices_ast) where

import Checking.Typechecking (checkTerm)
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
import Data.List (partition)



--check types in certain positions are the same
checkType:: [(Var, Type)] -> [Int] -> Type -> Bool
checkType argList indPosns ty = all (\i-> snd (argList !! i) == ty ) indPosns


--refactor the parameters of constructor
--remove redundant params
changeConstr_argsList:: [(Var, Type)] -> [Int] -> [(Var, Type)]
changeConstr_argsList argList [] = argList
changeConstr_argsList argList (i:indPosns) = 
    case argList !! i of 
        (var,ty) -> if checkType argList indPosns ty then --check that the indices we want to unify are of the same type
                        [argList!!j | j <- [0..(length argList)-1] , not (elem j indPosns)]  --remove redundant vars 
                    else 
                        argList


--rename the use of deleted vars in a type
replaceOldVar_type:: [Var] -> Var -> Type -> Type
replaceOldVar_type oldVars newVar (App t1 t2) = 
    App (replaceOldVar_type oldVars newVar t1) (replaceOldVar_type oldVars newVar t2)
replaceOldVar_type oldVars newVar (V var) = 
    if elem var oldVars then 
        V newVar
    else 
        V var
replaceOldVar_type oldVars newVar ty = ty 


--refactor the return type of the constructor
--rename unused var names with the unified one
changeConstr_retTy:: [(Var, Type)] -> [Int] -> Type -> Type
changeConstr_retTy argList [] retTy = retTy
changeConstr_retTy argList (i:indPosns) retTy =   
    case argList !! i of 
        (var,ty) -> let oldVars = [fst (argList!!j) | j <- indPosns] in
                        replaceOldVar_type oldVars var retTy


--refactor the constructor
--recurse to the constructor params and return type
changeConstr_constr:: [Int] -> CtorItem -> CtorItem
changeConstr_constr indPosns (CtorItem itemName ty dataName) = 
    case piTypeToList ty of 
        (argList, retTy) -> let l = length argList   
                                indPosnsRev = map (\i -> l-i) indPosns in 
                                if all (\x -> x<l) indPosnsRev then  -- indices positions valid
                                    let refactoredArgList = changeConstr_argsList argList indPosnsRev  --refactor indices
                                        refactoredRetType = changeConstr_retTy argList indPosnsRev retTy in --refactor return type
                                        (CtorItem itemName (listToPiType (refactoredArgList, refactoredRetType)) dataName)  
                                else  --some indices out of bounds
                                    (CtorItem itemName ty dataName)
            


--refactor the data
--recurse to the constructor
changeConstr_data ::  String -> String -> [Int] -> DataItem -> DataItem
changeConstr_data datName constrName indPosns (DataItem dname dty dConstrs) 
    = DataItem dname 
               dty
               (map (\constr -> if ctorItemName constr == constrName then 
                                    changeConstr_constr indPosns constr
                                else 
                                    constr
                    ) 
                    dConstrs
                ) 

--refactor the program
--recurse to the data type declaration
changeConstr_ast :: String -> String -> [Int] ->  Program ->  Program
changeConstr_ast datName constrName indPosns (Program itemL)= 
    Program 
        (map (\item -> 
            case item of 
                (Decl decl) -> Decl decl
                (Data dat) -> if dataName dat == datName then   
                                Data (changeConstr_data datName constrName indPosns dat)
                              else 
                                Data dat        
            )
            itemL
        )



---------------------------------------------------


--update the arguments to constructor
--fill with holes
updateUsecase_constrTerm:: [Term] -> [Int] -> [Term]
updateUsecase_constrTerm termList indPosns = 
    map (\i -> if elem (i+1) indPosns then
                    case termList!!i of 
                        V (Var str int) -> Hole (Var (str ++ "_" ++ show i ) int)  --hole name [oldname]_[position]
                        term -> term 
                else 
                    termList!!i            
    )
    [0..((length termList)-1)]


--update the use of refactored constructor, when it occurs in the rhs of equations
--if constructor in rhs, we remove the I\I1 indices, and make the I1 index a hole
updateUsecase_eqnrhs:: String -> [Int] -> Pat -> Pat
updateUsecase_eqnrhs constrName [] term = term
--TODO: recurse down if and case expressions 
updateUsecase_eqnrhs constrName (ind:inds) (Pair t1 t2) = 
    Pair (updateUsecase_eqnrhs constrName (ind:inds) t1) (updateUsecase_eqnrhs constrName (ind:inds) t2)
updateUsecase_eqnrhs constrName (ind:inds) (Lam lvar t2) = 
    Lam lvar (updateUsecase_eqnrhs constrName (ind:inds) t2) --TODO: need to check binding? or are we disallowing them in fluid?
--TODO: possible recurse down other constructor type (but since we're removing them, I'm ignoring them for now)
updateUsecase_eqnrhs constrName (ind:inds) (App t1 t2) = 
    let termList = appTermToList (App t1 t2) in 
        case last termList of 
            Global varName -> if varName == constrName then 
                                let holedConstr = updateUsecase_constrTerm termList (ind:inds) in
                                    listToAppTerm  [holedConstr!!j | j <- [0..(length holedConstr)-1] , not (elem (j+1) inds)]
                              else 
                                (App t1 t2)
updateUsecase_eqnrhs constrName indPosns term = term



--change nested App term to (reversed) list
appTermToList:: Term -> [Term]
appTermToList (App t1 t2) = t2:(appTermToList t1) 
appTermToList term = [term]
--change list to App term
listToAppTerm:: [Term] -> Term
listToAppTerm [term] = term 
listToAppTerm (term:terms) = App (listToAppTerm terms) term 



--TODO: add vars name if wildcards are used. Q: how to generate fresh variables?
removeWildcards :: [Term] -> [Term]
removeWildcards termList = termList  


--refactor use of constructor in a pattern variable
--removes unified parameters
--[term] to remmeber what vars were deleted and rename all uses of the these vars in the clause
    -- rename all other vars in term by the name of the first element
updateUsecase_pat:: String -> [Int] -> Pat -> (Pat, [Term])
updateUsecase_pat constrName [] (App t1 t2) = ((App t1 t2), [])
updateUsecase_pat constrName (ind:inds) (App t1 t2) =
    let termList = removeWildcards (appTermToList (App t1 t2)) in  --change wildcards to named vars
        case last termList of 
            Global varName -> if varName == constrName then 
                                let (toKeep, toRemove) = partition  (\j -> not (elem (j+1) inds))  [0..(length termList)-1] in
                                    (listToAppTerm [termList!!j | j <- toKeep] , (termList!!(ind-1)):[termList!!j | j <- toRemove])
                              else 
                                ((App t1 t2),[])
updateUsecase_pat constrName indPosns term = (term, [])


--refactor use of constructor in lhs of a equation
updateUsecase_pats:: String -> [Int] -> [Pat] -> ([Pat], [Term])
updateUsecase_pats constrName indPosns [] = ([],[])
updateUsecase_pats constrName indPosns (pat:pats) = 
    let (patRes, varsToRename1) = updateUsecase_pat constrName indPosns pat 
        (patRec, varsToRename2) = updateUsecase_pats constrName indPosns pats in 
        (patRes:patRec , varsToRename1 ++ varsToRename2 )        


--rename vars in a pattern 
renameVars_pat:: Term -> [Term] -> Pat -> Pat
renameVars_pat newVar varsToRename pat = 
    renameVars_term newVar varsToRename pat


--rename vars in lhs of equations
renameVars_pats:: Term -> [Term] -> [Pat] -> [Pat]
renameVars_pats newVar varsToRename [] = []
renameVars_pats newVar varsToRename (pat:pats) = 
    (renameVars_pat newVar varsToRename pat):(renameVars_pats newVar varsToRename pats)


--rename vars in rhs of equations
renameVars_term:: Term -> [Term] -> Term -> Term
renameVars_term newVar varsToRename (App term1 term2) = 
    App (renameVars_term newVar varsToRename term1) (renameVars_term newVar varsToRename term2) 
renameVars_term newVar varsToRename (Pair term1 term2) = 
    Pair (renameVars_term newVar varsToRename term1) (renameVars_term newVar varsToRename term2) 
renameVars_term newVar varsToRename (Lam lvar term2) = 
    Lam lvar (renameVars_term newVar varsToRename term2) --TODO: need to check binding? or are we disallowing them in fluid?
--TODO: possible recurse down other constructor type (but since we're removing them, I'm ignoring them for now)
--TODO: recurse through cases and ifs
renameVars_term newVar varsToRename (V var) = 
    if elem (V var) varsToRename then 
        newVar
    else 
        (V var)
renameVars_term newVar varsToRename term = term


--rename the use of deleted vars in an equation
--rename vars in term\term[0] in clause to var name in term[0]
--TODO: refactor this out to a general var rename refactoring
renameVars:: [Term] -> Clause -> Clause
renameVars [] clause = clause
renameVars (newVar:varsToRename) (Clause pats term) = 
    Clause (renameVars_pats newVar varsToRename pats) (renameVars_term newVar varsToRename term)
renameVars (newVar:varsToRename) (ImpossibleClause pats) = 
    ImpossibleClause (renameVars_pats newVar varsToRename pats) 



--update use cases in function equation
--update constructor arguments and rename use of deleted variables
updateUsecase_cl:: String -> [Int] -> Clause -> Clause
updateUsecase_cl constrName indPosns (Clause pats term) = 
    let (patRes, varsToRename) = updateUsecase_pats constrName indPosns pats 
        newClause = Clause (patRes) (updateUsecase_eqnrhs constrName indPosns term) in --constructor updated to remove indices
            renameVars varsToRename newClause --rename uses of removed vars 
updateUsecase_cl constrName indPosns (ImpossibleClause pats) = 
    let patRes = updateUsecase_pats constrName indPosns pats in      
        ImpossibleClause (fst patRes)


--update use cases in function equations
updateUsecase_cls:: String -> [Int] -> [Clause] -> [Clause] 
updateUsecase_cls constrName indPosns [] = []
updateUsecase_cls constrName indPosns (cl:cls) = 
    (updateUsecase_cl constrName indPosns cl):(updateUsecase_cls constrName indPosns cls)


--update use cases in functions
updateUsecase_decl:: String -> String -> [Int] -> DeclItem -> DeclItem
updateUsecase_decl datName constrName indPosns decl = 
    DeclItem (declName decl)
             (declTy decl) 
             (updateUsecase_cls constrName indPosns (declClauses decl) )

--update use cases
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


unifyIndices_ast :: String -> String -> [Int] ->  Program ->  Program
unifyIndices_ast datName constrName indPosns ast = 
    let dataRefactored = changeConstr_ast datName constrName indPosns ast in  --change data definition
        updateUsecase datName constrName indPosns dataRefactored              --update use case of changed constructor



