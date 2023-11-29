import Data.List.Elem

-- assume we have
data Unzip : List (Nat, Nat) -> List Nat -> List Nat -> Type where
    NilUZ : Unzip [] [] []
    ConsUZ : Unzip xs vs ws -> Unzip ((x,y) :: xs) (x :: vs) (y :: ws)


-- introduced proof in Var 
data Expr : (vars : List Nat) -> Type where    
        Num : (vars : List Nat) -> Nat -> Expr []  
        Var : (vars : List Nat) -> (n : Nat) -> Elem n vars -> Expr vars  
        Add : (vars : List Nat) ->  (Expr vars) -> (Expr vars) -> Expr vars  -- probably seperate to unify and remove params

lookupVar : (vars : List Nat) -> (x : Nat) -> (env : List (Nat, Nat)) -> (Elem x vars) -> Maybe Nat 
lookupVar (x::vars) x [] Here = Nothing 
lookupVar (v::vars) x [] (There p) = Nothing 
lookupVar (x::vars) x ((y,val)::ys) Here = if x == y then Just val 
                                                     else lookupVar (x::vars) x ys Here 
lookupVar (v::vars) x ((y,val)::ys) (There p) = if x == y then Just val 
                                                          else lookupVar (v::vars) x ys (There p)
        
eval : (vs, ws : List Nat) -> (vars : List Nat) -> (env : List (Nat, Nat)) -> (Expr vars) -> (Unzip env vs ws) -> Maybe Nat 
eval vs ws [] env (Num vars n) u = Just n 
eval vs ws vars env (Var vars x r) u = lookupVar vars x env r
eval vs ws vars env (Add vars e1 e2) u = case eval vs ws vars env e1 u of 
                            Just e1' => case eval vs ws vars env e2 u of 
                                            Just e2' => Just (plus e1' e2')
                                            Nothing  => Nothing 
                            Nothing => Nothing 
