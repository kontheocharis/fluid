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
        Add : (vars : List Nat) -> (Expr vars) -> (Expr vars)
               -> Expr vars 

-- remove vars and replace with vs 
lookupVar : (vs,ws : List Nat) -> (x : Nat) -> (env : List (Nat, Nat)) -> (Elem x vs) -> (Unzip env vs ws) -> Maybe Nat 
lookupVar [] [] x [] Here NilUZ impossible 
lookupVar [] [] x [] (There p) NilUZ impossible 
lookupVar (x::vs) (val::ws) x ((x,val)::ys) Here (ConsUZ i) =
    if x == x
        then Just val
        else lookupVar vs ws x ys ?hole i 
lookupVar (y::vs) (val::ws) x ((y,val)::ys) (There p) (ConsUZ i) = 
    if x == y
        then Just val 
        else lookupVar vs ws x ys p i


lookupVarCover : (vars : List Nat) -> (x : Nat) -> (env : List (Nat, Nat)) -> (Elem x vars) -> Maybe Nat
lookupVarCover vars x env p = case unzip env of 
                                 (vs ** ws ** r) => lookupVar vs ws x env ?p r 

eval : (vs, ws : List Nat) -> (env : List (Nat, Nat)) -> (Expr vs) -> (Unzip env vs ws) -> Maybe Nat 
eval [] [] [] (Num vars n) NilUZ = Just n 
-- if the introduced type has a covering function/decision procedure
eval vs ws env (Var vs x r) u = case unzip env of 
                                 (vs2 ** ws2 ** r2) => lookupVar vs2 ws2 x env ?p2 r2 -- unfolded.
eval [] [] [] (Add [] e1 e2) NilUZ = ?muchLater
eval [] [] [] (Add [] e1 e2) (ConsUZ u) = ?muchLater2
eval (x::vs) (y::ws) ((x,y)::env) (Add (x::vs) e1 e2) NilUZ impossible --    = ?muchMuchLater
eval (x::vs) (y::ws) ((x,y)::env) (Add (x::vs) e1 e2) (ConsUZ u) = ?muchMuchLater

eval (_ :: _) (_ :: _) (_ :: _) (Add (_ :: _) _ _) _ = ?k2

{-
case eval [] ws env e1 ?u1 of 
                            Just e1' => case eval vs ws env e2 ?u2 of 
                                            Just e2' => Just (plus e1' e2')
                                            Nothing  => Nothing 
                            Nothing => Nothing 
-}
       --  Add : (vs : List Nat) -> (v1 : List Nat) 
          -- -> (v2 : List Nat) -> (Expr v1) -> (Expr v2)
          -- -> (p : Union v1 v2 vs)
          -- -> Expr vs 

    -- Cons : (x : Nat) -> (xs, ys, zs : List Nat) -> Union xs ys zs -> Union (x :: xs) ys (x :: zs)
-- eval (x1::vs) (w::ws) ((x1,w)::env) (Add (x1::vs) (x1::v1) v2 e1 e2 (Cons x1 v1 v2 vs x5)) (ConsUZ z) = ?later

{-
case eval v1 ws env e1 ?u1 of 
                            Just e1' => case eval v2 ws env e2 ?u2 of 
                                            Just e2' => Just (plus e1' e2')
                                            Nothing  => Nothing 
                            Nothing => Nothing 
-}