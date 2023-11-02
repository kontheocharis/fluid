module Vars (var, Sub, sub, subVar, alphaRename) where

import Lang

-- | Helper function to create a variable without caring about the unique identifier.
var :: String -> Var
var x = Var x 0

-- | A substitution, represented as a list of variable-term pairs.
newtype Sub = Sub [(Var, Term)]

-- | Apply a substitution to a term.
sub :: Sub -> Term -> Term
sub (Sub []) t = t
sub (Sub ((v, t') : s)) t = sub (Sub s) (subVar v t' t)

-- | Substitute a variable for a term in a term.
subVar :: Var -> Term -> Term -> Term
subVar v t' =
  mapTerm
    ( \t'' -> case t'' of
        V v' | v == v' -> Just t'
        Hole v' | v == v' -> Just t'
        _ -> Nothing
    )

-- | Alpha rename a variable in a term.
alphaRename :: Var -> Var -> Term -> Term
alphaRename v1 v2 = subVar v1 (V v2)
