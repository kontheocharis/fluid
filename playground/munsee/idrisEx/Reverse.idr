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
-- reverse1 (S m') (x :: xs) = (reverse1 m' xs) ++ [x] --use let to make it easier to work with
reverse1 (S m') (x :: xs) = let ys = reverse1 m' xs 
                                in ys ++ [x]

-------------------------------------------------------------------------------
-- change output type

reverse2 : (m:Nat) -> Vect m a -> (k : Nat ** Vect k a) 
reverse2 Z [] = (Z ** [])
reverse2 (S m') (x :: xs) = let (k' ** ys) = reverse2 m' xs in 
                                    --(?hole ** (ys ++ [x]))
                                    --((S k') ** (ys ++ [x]))
                                    ((k'+ 1)  ** (ys ++ [x]))

-- needs the definition of ++ to find out that we need k'+1
-- we don'r need plusCommuttative here since we're using dep pair. If we claim k=m then we would need that.
-------------------------------------------------------------------------------
--let's see if we can solve recursion

len2 : (m:Nat) ->  Nat 
len2 Z  = Z 
--len2 (S m')  = let k' = len2 m'  in (k'+ 1)  -- clean up
len2 (S m')  = len2 m' + 1 

--need plusCommutative, maybe we can find that k=m?

-------------------------------------------------------------------------------
-- now suppose that we have the proof of m=k

reverse3 : (m:Nat) -> Vect m a -> (k:Nat) -> (p: k=m) -> (k : Nat ** Vect k a) 
reverse3 Z [] Z Refl = (Z ** [])
reverse3 (S m') (x :: xs) (S m') Refl = let (k' ** ys) = reverse3 m' xs m' Refl 
                                                 in ((k'+ 1)  ** (ys ++ [x]))

--casesplit on p is a bit weird???

--never need plusCommutative?
-------------------------------------------------------------------------------
--now remove Sigma

reverse4 : (m:Nat) -> Vect m a -> (k:Nat) -> (p: k=m) -> (Vect k a) 
reverse4 Z [] Z Refl = []
reverse4 (S m') (x :: xs) (S m') Refl =  rewrite (plusCommutative 1 m') 
                                                    in  (reverse4 m' xs m' Refl) ++ [x]


-------------------------------------------------------------------------------
--can we go further and remove the proof requirement?

--reverse5 : (m:Nat) -> Vect m a -> (Vect m a) 
--reverse5 Z [] = []
--reverse5 (S m') (x :: xs) =  rewrite (plusCommutative 1 m') 
--                                    in  (reverse5 m' xs ) ++ [x]

--remove m (maybe intermediate step is to retain as implicit argument first?)
--reverse6 : Vect m a -> (Vect m a) 
--reverse6 [] = []
--reverse6 {m=S m'} (x :: xs) =  rewrite (plusCommutative 1 m') 
--                                    in  (reverse6 xs) ++ [x]

