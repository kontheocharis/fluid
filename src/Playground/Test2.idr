module Test2

import Data.Nat
import Data.Fin
import Data.Vect
import Decidable.Equality
import RefacPrelude

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat Z Z = Just Refl
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing 
checkEqNat (S k) (S j) = case checkEqNat k j of 
                            Nothing => Nothing 
                            Just p  => Just (cong S p)



lteLem1 : (p1 : LTE n m) -> (p2 : LTE m n) -> n = m 
lteLem1 LTEZero LTEZero = Refl
lteLem1 (LTESucc n') (LTESucc m') = 
    let hyp = lteLem1 n' m'
    in cong S hyp

-- with eliminator
lteHelp2 : (m : Nat) -> (hyp : 0 = m) -> (0 = S m -> Void2)
lteHelp2 Z hyp = (\p => p1IsNot0 (sym p))
lteHelp2 (S m') hyp = (\p => pSnIsNot0 (S m') (sym p))



lteElHelp1' : ( m : Nat) -> (p2 : LTE m 0) -> 0 = m 
lteElHelp1' m p2 = 
    let ne = natElim (\m => (LTE m 0) -> 0 = m) 
                     (\p => Refl) 
                     (\z, hyp, p => ?u) -- boils down to same thing as lteElHelp1, abandoning...
    in ?body3


lteElHelp2' : ( m : Nat) -> (0 = m)   
lteElHelp2' m = 
    let ne = natElim (\m => 0 = m -> Void2) 
                     ?h2 
                     (\z, hyp, p => pSnIsNot0 z (sym p))
                    
    in ?body5

lteElHelp2 : ( m : Nat) -> (p2 : LTE m 0) -> 0 = m 
lteElHelp2 m p2 = 
    let ne = lteElim (\m,z,p => 0 = m) 
                     (\m => Refl) 
                     (\m,z,p,hyp => ?r)
    in ?body4

------------------------------------------------------------------------
NoConfusion : Nat -> Nat -> Type 
NoConfusion Z Z = Z = Z 
NoConfusion (S n) (S m) = n = m 
NoConfusion _ _ = Void2

noConf : (x , y : Nat) -> x = y -> NoConfusion x y 

apply3 : (a : Type) -> (x,y : a) -> (p : a -> Type) -> x = y -> p x -> p y
apply3 a x x p Refl px = px

antisym : (m,n : Nat) -> LTE m n -> LTE n m -> m = n 
antisym = lteElim (\m,n,_ => LTE n m -> m = n) 
                        (\n,e => lteElim (\n,m,_ => m = Z -> m = n)
                           (\n,e => e) 
                           (\k,l,_,_,e => voidElim (\_ => S l = S k) 
                                 (noConf (S l) Z e)) 
                            n Z e Refl )
                        (\m,n,_,h,q => cong S 
                           (h ( -- the following is basically fromLteSucc
                            lteElim (\k,l,_ => k = S n -> l = S m -> LTE n m)
                                    (\_,e,_ => voidElim (\_ => LTE n m) (noConf Z (S n) e))
                                    (\k,l,e,_,x,y => apply3 Nat k n (\n => LTE n m) (noConf (S k) (S n) x) (apply3 Nat l m (\m => LTE k m) (noConf (S l) (S m) y) e))
                                    (S n) (S m) q Refl Refl 
                        )))