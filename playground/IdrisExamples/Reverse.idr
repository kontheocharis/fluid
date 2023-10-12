module Reverse

import Data.Nat
import Data.Vect

reverse0 : List a -> List a
reverse0 [] = []
reverse0 (x :: xs) = (reverse0 xs) ++ [x]

-------------------------------------------------------------------------------
--Assume we have conversion

vectToList : Vect m a -> List a
vectToList [] = []
vectToList (x::xs) = x::(vectToList xs)


listToVect : (xs : List a) -> (m : Nat ** Vect m a)
listToVect []  =  (Z ** [])
listToVect (x::xs) = let (n**partialVect) = listToVect xs in 
                         ( (S n) ** x::partialVect) 
     
-------------------------------------------------------------------------------
-- change input type

reverse1 : (m:Nat) -> Vect m a -> List a
reverse1 Z [] = []
reverse1 (S m') (x :: xs) = let ys = reverse1 m' xs 
                                in ys ++ [x]

-------------------------------------------------------------------------------
-- change output type

reverse2 : (m:Nat) -> Vect m a -> (k : Nat ** Vect k a) 
reverse2 Z [] = (Z ** [])
reverse2 (S m') (x :: xs) = let (k' ** ys) = reverse2 m' xs in 
                                ((k'+ 1)  ** (ys ++ [x]))

-- needs the definition of ++ to find out that we need k'+1
-------------------------------------------------------------------------------
{-
--maybe we can try solving recursion with e.g. a CAS?
len2 : (m:Nat) ->  Nat 
len2 Z  = Z 
len2 (S m')  = len2 m' + 1 
--need plusCommutative, maybe we can find that k=m?
-}
-------------------------------------------------------------------------------
-- now suppose that we have the proof of m=k

reverse3 : (m:Nat) -> Vect m a -> (p: k=m) -> (k : Nat ** Vect k a) 
reverse3 Z [] p = (Z ** [])
reverse3 (S m') (x :: xs) Refl =  let (k' ** ys) = reverse3 m' xs Refl
                                        in ((k'+ 1)  ** (ys ++ [x]))

-------------------------------------------------------------------------------
--now remove Sigma

reverse4 : (m:Nat) -> Vect m a -> (p: k=m) -> (Vect k a) 
reverse4 Z [] p = rewrite p in []
reverse4 (S m') (x :: xs) Refl =  rewrite (plusCommutative 1 m') 
                                        in  (reverse4 m' xs Refl) ++ [x]


-------------------------------------------------------------------------------
