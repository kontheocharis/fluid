module Refactoring.SpecialiseConstructorIndex (specConstr_ast) where

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


specConstr_retType:: Type -> Int -> Term ->  Type
specConstr_retType (App t1 (V var)) 0 resTerm = App t1 resTerm  --can only specialise variables
specConstr_retType (App t1 t2) i resTerm = 
    if i < 1 then 
        (App t1 t2)
    else 
        App (specConstr_retType t1 (i-1) resTerm ) t2
specConstr_retType term i resTerm = term


specConstr_constr:: Int ->  Term ->  CtorItem -> CtorItem
specConstr_constr indPosn resTerm (CtorItem itemName ty dataName) = 
    case piTypeToList ty of 
        (list, retTy) -> CtorItem itemName 
                                  (listToPiType (list, specConstr_retType retTy indPosn resTerm)) 
                                  dataName


specConstr_data ::  String -> String -> Int -> Term -> DataItem -> DataItem
specConstr_data datName constrName indPosn resTerm (DataItem dname dty dConstrs) 
    = DataItem dname 
               dty
               (map (\constr -> if ctorItemName constr == constrName then 
                                    specConstr_constr indPosn resTerm constr
                                else 
                                    constr
                    ) 
                    dConstrs
                ) 

--given an indexed type, int i and a term, check that the the term is of type equal to the ith index 
checkTermTypeIsIthInd:: Type -> Int -> Term -> Bool
checkTermTypeIsIthInd ty indPosn resTerm = True 
--TODO: should check that the resTerm is of the right type (will do when have ASTs annotated with types)


specConstr_ast :: String -> String -> Int ->  Term ->  Program ->  Program
specConstr_ast datName constrName indPosn resTerm (Program itemL)= 
    Program 
        (map (\item -> 
            case item of 
                (Decl decl) -> Decl decl
                (Data dat) -> if dataName dat == datName then   
                                if checkTermTypeIsIthInd (dataTy dat) indPosn resTerm then 
                                    Data (specConstr_data datName constrName indPosn resTerm dat)
                                else 
                                    Data dat
                              else 
                                Data dat        
            )
            itemL
        )
{-
--Does not refactor use sites:

data Data1: Nat -> Type where
    | C : (n:Nat) -> Data1 n 

f: (n:Nat) -> Data1 n
f Z = ...
f (S n) = C (S n)

--will break when specialise index of C to Z

-}