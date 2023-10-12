module Span

import Data.Nat
import Data.Vect

--Assume we have conversion

vectToList : Vect m a -> List a
vectToList [] = []
vectToList (x::xs) = x::(vectToList xs)


listToVect : (xs : List a) -> (m : Nat ** Vect m a)
listToVect []  =  (Z ** [])
listToVect (x::xs) = let (n**partialVect) = listToVect xs in 
                         ( (S n) ** x::partialVect) 

-------------------------------------------------------------------------------
||| Given a predicate and a list, returns a tuple consisting of the longest
||| prefix of the list whose elements satisfy the predicate, and the rest of the
||| list.
span0 : (f: a -> Bool) -> List a -> (List a, List a)
span0 f []      = ([], [])
span0 f (x::xs) =
  if f x then
    let (ys, zs) = span0 f xs in
        (x::ys, zs)
  else
    ([], x::xs)

-------------------------------------------------------------------------------
-- change input type

span1 : (f: a -> Bool) -> (m : Nat) -> Vect m a  -> (List a, List a)
span1 f Z []      = ([], [])
span1 f (S m') (x::xs) =
  if f x then
    let (ys, zs) = span1 f m' xs in
        (x::ys, zs)
  else
    ([], x::(vectToList xs))

-------------------------------------------------------------------------------
-- change input type

span2 : (f: a -> Bool) -> (m : Nat) -> Vect m a  -> (List a, List a)
span2 f Z []      = ([], [])
span2 f (S m') (x::xs) =
  if f x then
    let (ys, zs) = span2 f m' xs in
        (x::ys, zs)
  else
    ([], x::(vectToList xs))

-------------------------------------------------------------------------------
-- change output types  

span3 : (f: a -> Bool) -> (m : Nat) -> Vect m a  -> ((k ** Vect k a), (l ** Vect l a) )
span3 f Z []      = ((Z**[]), (Z**[]))
span3 f (S m') (x::xs) =
  if f x then
    let ((k'** ys), (l' ** zs)) = span3 f m' xs in
        ( ((S k') ** x::ys), (l' ** zs))
  else
    ((Z ** []), ((S m') ** x::xs))


-------------------------------------------------------------------------------
-- as before, we have k <=m and l<=m  and l = m-k
-- as before, not sure how to use it ....