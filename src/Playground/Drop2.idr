module Drop2 

import Data.Nat
import Data.Fin 
import Data.Vect

import RefacPrelude

vectToList : Vect n a -> List a 
vectToList xs = toList xs


drop3 : (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m)
     -> (k : Nat ** Vect k a)
drop3 Z m xs p = (m ** xs)
drop3 (S n') Z [] p = (Z ** []) -- technically impossible
                                -- but if we don't pattern match...
drop3 (S n') (S m') (x :: xs) (LTESucc p') = drop3 n' m' xs p'
                                -- we need to pass something to the recursive
                                -- call, so we case split
                                -- here, we have only one possibility b/c
                                -- of the arguments, and it becomes obvious what
                                -- to plug in

-------------------------------------------------------------------------------------------------------
drop4PE : (a : Type) -> (n' : Nat) -> (xsTM : Nat) -> Vect xsTM a -> (pSN'SSxsTM : LTE (S n') (S xsTM))
       -> (rec : (m : Nat) -> Vect m a -> LTE n' m -> (k : Nat ** Vect k a))
       -> (k : Nat ** Vect k a)
drop4PE a n' xsTM xs' pSN'SSxsTM rec = 
    let lteE = lteElim (\l,r, pSN'SSxsTM => (k : Nat ** Vect k a))
                       (\r => ?hole1) -- what do we put here?
                       (\l,r,p, lTErec => rec xsTM xs' (fromLteSucc pSN'SSxsTM))
    in lteE (S n') (S xsTM) pSN'SSxsTM


drop4'V : (a : Type) -> (n' : Nat) -> (m' : Nat) -> Vect (S m') a -> (pSN'SZ : LTE (S n') (S m'))
        -> (rec : (m : Nat) -> Vect m a -> LTE n' m -> (k : Nat ** Vect k a))
        -> (k : Nat ** Vect k a)
drop4'V a n' m' xs pSN'SZ rec = 
    let vE = vecElim a (\m', xs => (pSN'SZ : LTE (S n') m') -> (k : Nat ** Vect k a))
                       (\pSM'1 => (Z ** []))
                       (\xsTM, a', xs', vRec, pSN'SSxsTM => drop4PE a n' xsTM xs' pSN'SSxsTM rec)
    in vE (S m') xs pSN'SZ


drop4M'E : (a : Type) -> (n' : Nat) -> (m : Nat) -> Vect m a -> (pSN' : LTE (S n') m)
     -> (rec : (m : Nat) -> Vect m a -> LTE n' m -> (k : Nat ** Vect k a))
     -> (k : Nat ** Vect k a)
drop4M'E a n' m xs pSN' rec =
    let natEM = natElim (\m => Vect m a -> (pSN' : LTE (S n') m) -> (k : Nat ** Vect k a))
                        (\xsEmpty, pSN'Z => (Z ** []))
                        (\m', m'Rec, xs, pSN'SZ => drop4'V a n' m' xs pSN'SZ rec)
    in natEM m xs pSN'


drop4 : (a : Type) -> (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m)
     -> (k : Nat ** Vect k a)
drop4 a n m xs p = 
    let natEN = natElim (\n => (m : Nat) -> Vect m a -> (p : LTE n m) -> (k : Nat ** Vect k a))  
                       (\m, xs, pLZ => (m ** xs) ) 
                       (\n', rec, m, xs, pSN' => drop4M'E a n' m xs pSN' rec)
    in natEN n m xs p