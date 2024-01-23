module Refactoring.RemoveMaybe (removeMaybe_ast) where

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



--remove Just in a term
removeJust_term:: Term -> Term 
removeJust_term (App term1 term2) = App (removeJust_term term1) (removeJust_term term2) 
removeJust_term (Lam var term2) = Lam var (removeJust_term term2) 
removeJust_term (Pair term1 term2) = Pair (removeJust_term term1) (removeJust_term term2) 
--TODO: recurse down case expressions
removeJust_term (MJust term) = (term) 
removeJust_term term = term


--remove Just in the equations
removeJust_cls:: [Clause] -> [Clause] 
removeJust_cls cls = map (\cl -> case cl of 
                              (ImpossibleClause pats) ->  ImpossibleClause pats
                              (Clause pats term) -> Clause pats (removeJust_term term)
                         ) 
                     cls

--remove Maybe from the return type
removeMaybe_sig:: Type -> Type 
removeMaybe_sig ty = let (inpTy, resTy) = piTypeToList ty in 
                         case resTy of 
                            MaybeT ty -> listToPiType (inpTy, ty) 
                            ty -> listToPiType (inpTy, resTy) 


--check if term do not have Nothing
onlyJust_term :: Term -> Bool
onlyJust_term (App term1 term2) = (onlyJust_term term1) && (onlyJust_term term2) 
onlyJust_term (Lam var term2) = (onlyJust_term term2) 
onlyJust_term (Pair term1 term2) =  (onlyJust_term term1) && (onlyJust_term term2) 
onlyJust_term (MJust term) = (onlyJust_term term) 
onlyJust_term MNothing = False
onlyJust_term term = True
--TODO: recurse through case

--check if the rhs of equations do not have Nothing
  --TODO: need to rethink if we allow Maybe type elsewhere
onlyJust:: DeclItem -> Bool 
onlyJust decl = all (\cl -> case cl of 
                              (ImpossibleClause pats) ->  True
                              (Clause pats term) -> onlyJust_term term
                    ) 
                    (declClauses decl) 


--refactor function
removeMaybe_func :: String -> DeclItem ->  DeclItem
removeMaybe_func funcName decl = 
    let (inpTys, resTy) = piTypeToList (declTy decl) in 
        case resTy of --check return type is a Maybe
            MaybeT ty -> if onlyJust decl then 
                            DeclItem (declName decl) (removeMaybe_sig (declTy decl)) (removeJust_cls (declClauses decl))
                         else 
                            decl
            otherTy -> decl


--refactor the program
--recurse to function
removeMaybe_ast :: String -> Program ->  Program
removeMaybe_ast funcName (Program itemL)= 
    Program 
        (map (\item -> 
            case item of 
                (Decl decl) -> if (declName decl) == funcName then 
                                    Decl (removeMaybe_func funcName decl)
                                else 
                                    Decl decl
                (Data dat) -> Data dat        
            )
            itemL
        )
