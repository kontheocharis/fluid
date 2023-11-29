import Data.List.Elem

-- introduced proof in Var 
data Expr : (vars : List Nat) -> Type where    
        Num : (vars : List Nat) -> Nat -> Expr []  
        Var : (vars : List Nat) -> (n : Nat) -> Elem n vars -> Expr vars  
        Add : (vars : List Nat) ->  (Expr vars) -> (Expr vars) -> Expr vars  -- probably seperate to unify and remove params

lookupVar : (x : Nat) -> (env : List (Nat, Nat)) -> Maybe Nat 
lookupVar x [] = Nothing 
lookupVar x ((y,val)::ys) = if x == y then Just val 
                                      else lookupVar x ys

eval : (vars : List Nat) -> (env : List (Nat, Nat)) -> (Expr vars) -> Maybe Nat 
eval [] env (Num vars n) = Just n 
eval vars env (Var vars x r) = lookupVar x env 
eval vars env (Add vars e1 e2) = case eval vars env e1 of 
                            Just e1' => case eval vars env e2 of 
                                            Just e2' => Just (plus e1' e2')
                                            Nothing  => Nothing 
                            Nothing => Nothing 
