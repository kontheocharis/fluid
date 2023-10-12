module Partition
import Decidable.Equality


import Data.Vect
{-data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a
%name Vect xs, ys, zs
-}

%default total
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

partition0 : (f : a -> Bool) -> (xs : List a) -> (List a, List a)
partition0 f []      = ([], [])
partition0 f (x::xs) =
  let (lefts, rights) = partition0 f xs in
    if f x then
      (x::lefts, rights)
    else
      (lefts, x::rights)

-------------------------------------------------------------------------------
-- change input types

partition1 : (f : a -> Bool) -> (m: Nat) -> (xs : Vect m a) -> (List a, List a)
partition1 f Z []      = ([], [])
partition1 f (S m') (x::xs) =
  let (lefts, rights) = partition1 f m' xs in
    if f x then
      (x::lefts, rights)
    else
      (lefts, x::rights)

-------------------------------------------------------------------------------
-- change output type 1

partition2 : (f : a -> Bool) -> (m: Nat) -> (xs : Vect m a) -> ((k ** Vect k a), List a) 
partition2 f Z []      = ((Z**[]), [])
partition2 f (S m') (x::xs) =
  let ((k' ** lefts), rights) = partition2 f m' xs in
    if f x then
      ( ((S k') ** x::lefts), rights)
    else
      ( (k' ** lefts), x::rights)

-------------------------------------------------------------------------------
-- change output type 2

partition3 : (f : a -> Bool) -> (m: Nat) -> (xs : Vect m a) -> ((k ** Vect k a), (l ** Vect l a)) 
partition3 f Z []      = ((Z**[]), (Z**[]))
partition3 f (S m') (x::xs) =
  let ((k' ** lefts), (l' ** rights)) = partition3 f m' xs in
    if f x then
      ( ((S k') ** x::lefts), (l' ** rights))
    else
      ( (k' ** lefts), ( (S l') ** x::rights))

--like filter, this is done and we should stop here
-------------------------------------------------------------------------------

{-
-- can we push further???

len3 : (f : a -> Bool) -> (m: Nat) -> (Nat , Nat) 
len3 f Z      = (Z, Z)
len3 f (S m') =
  let (k', l' ) = len3 f m'  in
    if f x then
      ( S k', l')
    else
      ( k' , S l')

len3T : (f : a -> Bool) -> (m: Nat) -> (Nat , Nat) 
len3T f Z      = (Z, Z)
len3T f (S m') =
  let (k', l' ) = len3T f m'  in
    ( S k', l')

len3F : (f : a -> Bool) -> (m: Nat) -> (Nat , Nat) 
len3F f Z      = (Z, Z)
len3F f (S m') =
  let (k', l' ) = len3F f m'  in
    ( k' , S l')

--Can we ever solve for recursion here? 
--let's project to k first

len3Tk : (f : a -> Bool) -> (m: Nat) -> Nat
len3Tk f Z = Z
--len3Tk f (S m') = let k' = len3Tk f m'  in S k'
len3Tk f (S m') = S (len3Tk f m')

len3Fk : (f : a -> Bool) -> (m: Nat) -> Nat  
len3Fk f Z      = Z
len3Fk f (S m') = len3Fk f m'  

--as in filter, we shall get 0<=k<=m
-- but we can't use inequality to remove Sigma


--similarly, we can get 0<=l<=m
--But there is also k+l=m 
-- that could be useful. 
-}
-------------------------------------------------------------------------------

-- Q: how to find l=m-k ???
-- Q: how do we know if our Sigma can be removed? User must say why

-------------------------------------------------------------------------------
{-
-- suppose that user gives us l=m-k

partition4 : (f : a -> Bool) -> (m: Nat) -> (xs : Vect m a) -> (q : l= m `minus` k)-> ((k ** Vect k a), (l ** Vect l a)) 
partition4 f Z [] q  = ((Z**[]), (Z**[]))
partition4 f (S m') (x::xs) q = case q of Refl => let ((k' ** lefts), (l' ** rights)) = partition4 f m' xs ?hole in
                                                        if f x then
                                                        ( ((S k') ** x::lefts), (l' ** rights))
                                                        else
                                                        ( (k' ** lefts), ( (S l') ** x::rights))

-- can we replace l as m-k at all? Unlike drop, k is unknown a priori...

-------------------------------------------------------------------------------
myPartition : (f : a -> Bool) -> (m : Nat) -> (xs : Vect m a) -> ((k ** Vect k a), Vect (m `minus` k) a) 
myPartition f Z []      = ((Z ** []), [])
myPartition f (S m') (x::xs) =
    if f x then
        let ((leftLen ** lefts), rights) = myPartition f m' xs in -- rights : Vect (minus m' ?k) a -- can't deduce leftLen?
            ((S leftLen ** x::lefts), rights)   --need to rewrite hole with k= S leftLen, 
                                                --then we have |hole| = (S m') - (S leftLen) = ... = m' - leftLen = |rights|
    else
        let ((leftLen ** lefts), rights) = myPartition f m' xs in
            ((leftLen ** lefts), ?hole2)

-}
-------------------------------------------------------------------------------
-- GOAL
{-
myPartition : (f : a -> Bool) -> (xs : Vect m a) -> ((k ** Vect k a), (l ** Vect l a)) 
myPartition f []      = ((Z ** []), (Z** []))
myPartition f (x::xs) =
  let ((leftLen ** lefts), (rightLen ** rights)) = myPartition f xs in
    if f x then
      ((S leftLen ** x::lefts), (rightLen ** rights))
    else
      ((leftLen ** lefts), (S rightLen ** x::rights))
-}
-----------