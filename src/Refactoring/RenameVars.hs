module Refactoring.RenameVars (renameVars_clause, renameVars_term) where

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





--rename vars in a lhs of eqn
renameVars_pats:: String -> String -> [Pat] -> [Pat]
renameVars_pats oldVar newVar = map (\term -> renameVars_term oldVar newVar term)


--rename vars in a term
renameVars_term:: String -> String -> Term -> Term
renameVars_term oldVar newVar (App term1 term2) = 
    App (renameVars_term oldVar newVar term1) (renameVars_term oldVar newVar term2) 
renameVars_term oldVar newVar (Pair term1 term2) = 
    Pair (renameVars_term oldVar newVar term1) (renameVars_term oldVar newVar term2) 
renameVars_term oldVar newVar (Lam (Var name id) term) =
    if name == newVar then
        let newName = name ++ "_renamed" 
            alphaTerm = (Lam (Var newName id) (renameVars_term name newName term)) in 
            renameVars_term oldVar newVar alphaTerm 
    else 
        (Lam (Var name id) term) 
--TODO: possible recurse down other constructor type (but since we're removing them, I'm ignoring them for now)
--TODO: recurse through cases and ifs
renameVars_term oldVar newVar (V (Var varname id)) = 
    if varname ==  oldVar then 
        V (Var newVar id)
    else 
        (V (Var varname id))
renameVars_term oldVar newVar term = term

------------------------------------------



--rename vars in clause 
renameVars_clause:: String -> String -> Clause -> Clause
renameVars_clause oldVar newVar (Clause lhs rhs) = Clause (renameVars_pats oldVar newVar lhs) (renameVars_term oldVar newVar rhs)
renameVars_clause oldVar newVar (ImpossibleClause lhs) = ImpossibleClause (renameVars_pats oldVar newVar lhs) 