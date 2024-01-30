module Refactoring.RemoveMaybe (removeMaybe) where

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
    TermValue (..),
    Type,
    Var (..),
    piTypeToList,
    listToPiType
  )
import Refactoring.Utils (FromRefactorArgs (..), Refact, lookupExprArg, lookupIdxArg, lookupNameArg)



--remove Just in a term
removeJust_term:: Term -> Term 
removeJust_term (Term (Case cterm ptList) termDat) = Term (Case cterm (map (\pair -> ((fst pair), removeJust_term (snd pair))) ptList)) termDat 
removeJust_term (Term (MJust term) termDat) = term 
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
                            Term (MaybeT ty) _ -> listToPiType (inpTy, ty) 
                            ty -> listToPiType (inpTy, resTy) 




--check if term do not have Nothing
onlyJust_term :: Term -> Bool
onlyJust_term (Term (App term1 term2) termDat) = (onlyJust_term term1) && (onlyJust_term term2) 
onlyJust_term (Term (Lam var term2) termDat) = (onlyJust_term term2) 
onlyJust_term (Term (Pair term1 term2) termDat) =  (onlyJust_term term1) && (onlyJust_term term2) 
onlyJust_term (Term (MJust term) termDat) = (onlyJust_term term)  
onlyJust_term (Term (Case cterm ptList) termDat) = all  (\pair -> onlyJust_term (snd pair)) ptList
onlyJust_term (Term MNothing termDat) = False
onlyJust_term term = True



--check if the rhs of equations do not have Nothing
  --TODO: need to rethink if we allow Maybe type elsewhere
onlyJust:: DeclItem -> Bool 
onlyJust decl = all (\cl -> case cl of 
                              (ImpossibleClause pats) ->  True
                              (Clause pats term) -> onlyJust_term term
                    ) 
                    (declClauses decl) 


--refactor function
removeMaybe_func :: DeclItem ->  DeclItem
removeMaybe_func decl = 
    let (inpTys, resTy) = piTypeToList (declTy decl) in 
        case resTy of --check return type is a Maybe
            Term (MaybeT ty) termDat -> if onlyJust decl then 
                                            DeclItem (declName decl) (removeMaybe_sig (declTy decl)) (removeJust_cls (declClauses decl))
                                        else 
                                            decl
            otherTy -> decl



data RemMaybeArgs = RemMaybeArgs
  { -- | The name of the function that has Maybe as return type
    removeMaybeFuncName :: String
  }

instance FromRefactorArgs RemMaybeArgs where
  fromRefactorArgs args =
    RemMaybeArgs
      <$> lookupNameArg "func" args


removeMaybe :: RemMaybeArgs -> Program -> Refact Program
removeMaybe args (Program itemL)= 
  return 
    (Program 
      (map (\item -> 
          case item of 
              (Decl decl) -> if (declName decl) == (removeMaybeFuncName args) then 
                                  Decl (removeMaybe_func decl)
                              else 
                                  Decl decl
              (Data dat) -> Data dat        
          )
          itemL
      ))

--stack run -- -r examples/testRemoveMaybe.fluid -n remove-maybe -a 'func=f'