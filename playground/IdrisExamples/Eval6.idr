import Data.List.Elem

-- assume we have
data Union : List Nat -> List Nat -> List Nat -> Type where 
    Nil : (ys: List Nat) -> Union [] ys ys 
    Cons : (x : Nat) -> (xs, ys, zs : List Nat) -> Union xs ys zs -> Union (x :: xs) ys (x :: zs)

-- introduced proof in Var 
data Expr : (vars : List Nat) -> Type where    
        Num : (vars : List Nat) -> Nat -> Expr []  
        Var : (vars : List Nat) -> (n : Nat) -> Elem n vars -> Expr vars  
        Add : (vars : List Nat) -> (vars1 : List Nat) 
          -> (vars2 : List Nat) -> (Expr vars1) -> (Expr vars2)
          -> (p : Union vars1 vars2 vars)
          -> Expr vars 

lookupVar : (vars : List Nat) -> (x : Nat) -> (env : List (Nat, Nat)) -> (Elem x vars) -> Maybe Nat 
lookupVar vars x [] p = Nothing 
lookupVar vars x ((y,val)::ys) p = if x == y then Just val 
                                             else lookupVar vars x ys p

eval : (vars : List Nat) -> (env : List (Nat, Nat)) -> (Expr vars) -> Maybe Nat 
eval [] env (Num vars n) = Just n 
eval vars env (Var vars x r) = lookupVar vars x env r 
eval vars env (Add vars v1 v2 e1 e2 p) = case eval v1 env e1 of 
                            Just e1' => case eval v2 env e2 of 
                                            Just e2' => Just (plus e1' e2')
                                            Nothing  => Nothing 
                            Nothing => Nothing 
