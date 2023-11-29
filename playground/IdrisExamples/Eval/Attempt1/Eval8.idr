import Data.List.Elem

-- assume we have
data Union : List Nat -> List Nat -> List Nat -> Type where 
    Nil : (ys: List Nat) -> Union [] ys ys 
    Cons : (x : Nat) -> (xs, ys, zs : List Nat) -> Union xs ys zs -> Union (x :: xs) ys (x :: zs)

-- assume we have
data Unzip : List (Nat, Nat) -> List Nat -> List Nat -> Type where
    NilUZ : Unzip [] [] []
    ConsUZ : Unzip xs vs ws -> Unzip ((x,y) :: xs) (x :: vs) (y :: ws)

unzip : (xs : List (Nat, Nat)) -> (vs ** (ws ** Unzip xs vs ws))
unzip [] = ([] ** ([] ** NilUZ))
unzip ((x,y) :: xs) = case unzip xs of
    (vs ** (ws ** p)) => ((x :: vs) ** ((y :: ws) ** ConsUZ p))

-- introduced proof in Var 
data Expr : (vars : List Nat) -> Type where    
        Num : (vars : List Nat) -> Nat -> Expr []  
        Var : (vars : List Nat) -> (n : Nat) -> Elem n vars -> Expr vars  
        Add : (vars : List Nat) -> (vars1 : List Nat) 
          -> (vars2 : List Nat) -> (Expr vars1) -> (Expr vars2)
          -> (p : Union vars1 vars2 vars)
          -> Expr vars 

lookupVar : (vs,ws : List Nat) -> (vars : List Nat) -> (x : Nat) -> (env : List (Nat, Nat)) -> (Elem x vars) -> (Unzip env vs ws) -> Maybe Nat 
lookupVar [] [] (x::vars) x [] Here NilUZ = Nothing 
lookupVar [] [] (v::vars) x [] (There p) NilUZ = Nothing 
lookupVar (y::vs) (val::ws) (x::vars) x ((y,val)::ys) Here (ConsUZ i) =
    if x == y
        then Just val
        else lookupVar vs ws (x::vars) x ys Here i 
lookupVar (y::vs) (val::ws) (v::vars) x ((y,val)::ys) (There p) (ConsUZ i) = 
    if x == y
        then Just val 
        else lookupVar vs ws (v::vars) x ys (There p) i


eval : (vars : List Nat) -> (env : List (Nat, Nat)) -> (Expr vars) -> Maybe Nat 
eval [] env (Num vars n) = Just n 
-- if the introduced type has a covering function/decision procedure
eval vars env (Var vars x r) = lookupVar ?vs ?ws vars x env r ?hPanic
eval vars env (Add vars v1 v2 e1 e2 p) = case eval v1 env e1 of 
                            Just e1' => case eval v2 env e2 of 
                                            Just e2' => Just (plus e1' e2')
                                            Nothing  => Nothing 
                            Nothing => Nothing 