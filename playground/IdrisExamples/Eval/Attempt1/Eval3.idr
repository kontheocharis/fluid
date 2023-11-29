import Data.List

data Expr : (vars : List Nat) -> Type where    
        Num : (vars : List Nat) -> Nat -> Expr []  
        Var : (vars : List Nat) -> Nat -> Expr vars  
        Add : (vars : List Nat) -> (vars1 : List Nat) 
          -> (vars2 : List Nat) -> (Expr vars1) -> (Expr vars2) -> Expr vars 

lookupVar : (x : Nat) -> (env : List (Nat, Nat)) -> Maybe Nat 
lookupVar x [] = Nothing 
lookupVar x ((y,val)::ys) = if x == y then Just val 
                                      else lookupVar x ys

eval : (vars : List Nat) -> (env : List (Nat, Nat)) -> (Expr vars) -> Maybe Nat 
eval [] env (Num vars n) = Just n 
eval vars env (Var vars x) = lookupVar x env 
eval vars env (Add vars v1 v2 e1 e2) = case eval v1 env e1 of 
                            Just e1' => case eval v2 env e2 of 
                                            Just e2' => Just (plus e1' e2')
                                            Nothing  => Nothing 
                            Nothing => Nothing 