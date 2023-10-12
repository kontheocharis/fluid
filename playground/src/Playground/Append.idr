module Append

import Data.Nat
import Data.Fin 
import Data.Vect

import RefacPrelude

vectToList : Vect n a -> List a 
vectToList xs = toList xs

{-
||| Append two lists
(++) : List a -> List a -> List a
(++) []      right = right
(++) (x::xs) right = x :: (xs ++ right)
-}

listAppend : (a : Type) -> List a -> List a -> List a 
listAppend a xs ys = 
        let elim = listElim a (\l => List a -> List a) (\ys => ys) (\x,xs,rec,ys => x :: (rec ys)) xs
        in elim ys


-- 1. change input parameter.
-- there are two to change...
--- 1, change first argument to vect of some length n
listAppend2 : (a : Type) -> (n : Nat) -> Vect n a -> List a -> List a 
listAppend2 a n xs ys = 
        let elim = listElim a (\l => List a -> List a) (\ys => ys) (\x,xs,rec,ys => x :: (rec ys)) (vectToList xs)
        in elim ys

-- 2. remove vectToList 
-- vecElim requires an additional parameter in the type function for the
-- length of the list.
-- This argument is also present in the cons case.
-- the length of the argument, xs, must also be passed. 
listAppend3 : (a : Type) -> (n : Nat) -> Vect n a -> List a -> List a 
listAppend3 a n xs ys = 
        let elim = vecElim a (\n,l => List a -> List a) (\ys => ys) (\a,x,xs,rec,ys => x :: (rec ys)) n xs
        in elim ys

--- 3. change input parameter
--- change second argument to a vect.
listAppend4 : (a : Type) -> (n : Nat) -> Vect n a -> (m : Nat) -> Vect m a -> List a 
listAppend4 a n xs m ys = 
        let elim = vecElim a (\n,l => List a -> List a) (\ys => ys) (\a,x,xs,rec,ys => x :: (rec ys)) n xs
        in elim (vectToList ys)

---- 4. remove vectToList
----- This requires the type List a to change to (m : Nat) -> Vect m a in argument to vecElim... 
----- vectToList must be applied to ys in the [] position
----- this conversion is not needed in the cons case as rec is already of list type
----- and x is of type a 
----- m needs to be passed to the eliminator
listAppend5 : (a : Type) -> (n : Nat) -> Vect n a -> (m : Nat) -> Vect m a -> List a 
listAppend5 a n xs m ys = 
        let elim = vecElim a 
                           (\n,l => (m : Nat) -> Vect m a -> List a) 
                           (\m,ys => (vectToList ys)) 
                           (\a,x,xs,rec,m,ys => x :: rec m ys)  
                           n xs
        in elim m ys


----- 5. Change the result type to a vector. 
----- We use a DP as we do not know what size it will be.
listAppend6 : (a : Type) -> (n : Nat) -> Vect n a -> (m : Nat) -> Vect m a ->  (o ** Vect o a) 
listAppend6 a n xs m ys = 
        let elim = vecElim a (\n,l => (m : Nat) -> Vect m a -> (o ** Vect o a)) (\m,ys => (m ** ys)) (\a',x,xs,rec,m,ys =>    
                sigElim Nat (\o => Vect o a)
                            (\a' => (o : Nat ** Vect o a)) -- watch that a' is fresh (it is not the type supplied to vect.
                            (\o,vo => (S o ** x :: vo)) (rec m ys)
             )  
             n xs
        in elim m ys


-- 6. Remove DP and replace with a constraint
listAppend7 : (a : Type) -> (n : Nat) -> Vect n a -> (m : Nat) -> Vect m a ->  (Vect (n+m) a) 
listAppend7 a n xs m ys = 
        let elim = vecElim a (\n,l => (m : Nat) -> Vect m a -> Vect (n+m) a) 
                                (\m,ys =>  ys)
                                (\a',x,xs,rec,m,ys => x :: rec m ys)
                                n xs
        in elim m ys

-- vecAppend' : (a : Type) -> (n : Nat) -> Vect n a -> (m : Nat) -> Vect m a -> Vect (n+m) a
-- vecAppend' a Z [] m v2 = v2
-- vecAppend' a (S n) (x :: xs) m v2 = x :: (vecAppend' a n xs m v2)

{-
vecAppend : (a : Type) -> (n : Nat) -> V
vecAppend a n v1 m v2 = 
        let elim = vecElim a (\n,ve => (m:Nat) -> Vect m a -> Vect (n+m) a) 
                              -- empty vec case
                              (\n,v2' => v2')
                              -- cons case 
                              (\t,x,xs,rec,m',v2' => x :: rec m' v2')
        in elim n v1 m v2
-}

drop : (n : Nat) -> (m : Nat) -> Vect m a -> (LTE m n) -> (k ** Vect k a) 
drop Z m xs prf            = (m ** xs)
drop (S n') Z [] prf       = (Z ** [])
drop (S n') (S m') (x :: xs) (LTESucc p) = drop n' m' xs p