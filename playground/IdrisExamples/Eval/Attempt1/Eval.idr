import Data.List

data Expr : (vars : List Nat) -> Type where    
        Num : (vars : List Nat) -> Nat -> Expr vars  
      | Var : (vars : List Nat) -> Nat -> Expr vars  
      | Add : (vars : List Nat) -> (vars1 : List Nat) 
          -> (vars2 : List Nat) -> (Expr vars1) -> (Expr vars2) -> Expr vars 

lookupVar : (x : Nat) -> (env : List (Nat, Nat)) -> Maybe Nat 
lookupVar x [] = Nothing 
lookupVar x ((y,val)::ys) = if x == y then Just val 
                                      else lookupVar x ys

eval : (env : List (Nat, Nat)) -> Expr -> Maybe Nat 
eval env (Num n) = Just n 
eval env (Var x) = lookupVar x env 
eval env (Add e1 e2) = case eval env e1 of 
                            Just e1' => case eval env e2 of 
                                            Just e2' => Just (plus e1' e2')
                                            Nothing  => Nothing 
                            Nothing => Nothing 
