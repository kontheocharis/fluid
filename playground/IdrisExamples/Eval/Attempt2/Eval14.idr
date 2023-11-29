import Data.List.Elem

-- assume we have
data Unzip : List (Nat, Nat) -> List Nat -> List Nat -> Type where
    NilUZ : Unzip [] [] []
    ConsUZ : Unzip xs vs ws -> Unzip ((x,y) :: xs) (x :: vs) (y :: ws)


-- introduced proof in Var 
data Expr : (vars : List Nat) -> Type where    
        Num : Nat -> Expr []  
        Var : (vars : List Nat) -> (n : Nat) -> Elem n vars -> Expr vars  
        Add : (vars : List Nat) ->  (Expr vars) -> (Expr vars) -> Expr vars  -- probably seperate to unify and remove params

lookupVar : (vars : List Nat) -> (x : Nat) -> (env : List (Nat, Nat)) -> (Elem x vars) -> (Unzip env vars ws) -> Maybe Nat 
lookupVar (x::vars) x [] Here u = Nothing 
lookupVar (v::vars) x [] (There p) u = Nothing 
lookupVar (y::vars) y ((y,val)::ys) Here (ConsUZ u) = if y == y then Just val 
                                                     else lookupVar (y::vars) y ys ?proof1 ?proof2 
lookupVar (v::vars) x ((v,val)::ys) (There p) (ConsUZ u) = if x == v then Just val 
                                                          else lookupVar (vars) x ys p u -- how do we adjust this automatically?
        
-- we discover vars is not related in the unzip... need to undo and make vs and vars the same...
eval : (ws : List Nat) -> (vars : List Nat) -> (env : List (Nat, Nat)) -> (Expr vars) -> (Unzip env vars ws) -> Maybe Nat 
eval [] [] [] (Num n) (NilUZ) = Just n 
eval [] [] [] (Var [] x Here) NilUZ impossible -- = lookupVar (x::vars) x env Here
eval (y::ws) (x::vars) ((x,y)::env) (Var (x::vars) x Here) (ConsUZ u) = lookupVar (x::vars) x ((x,y)::env) Here (ConsUZ u)
eval [] [] [] (Var (x'::[]) x (There p)) NilUZ impossible -- = lookupVar (x'::[]) x [] (There p)
eval (y::ws) (x'::vars) ((x',y)::env) (Var (x'::vars) x (There p)) (ConsUZ u) = lookupVar (x'::vars) x ((x',y)::env) (There p) (ConsUZ u)
eval ws vars env (Add vars e1 e2) u = case eval ws vars env e1 u of 
                            Just e1' => case eval ws vars env e2 u of 
                                            Just e2' => Just (plus e1' e2')
                                            Nothing  => Nothing 
                            Nothing => Nothing 
