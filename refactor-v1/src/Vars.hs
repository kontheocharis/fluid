module Vars (var) where

import Lang

-- | Helper function to create a variable without caring about the unique identifier.
var :: String -> Var
var x = Var x 0

-- | Properly set unique identifiers for variables in a term.
setUniqueVars :: Term -> Term
setUniqueVars = error "TODO: setUniqueVars"
