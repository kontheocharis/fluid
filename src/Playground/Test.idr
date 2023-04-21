module Test

import Data.Nat
import Data.Fin
import Data.Vect

natElim : (x : Nat -> Type) 
       -> (y : x Z)
       -> ((z : Nat) -> (a : x z) -> x (S z))
       -> (k : Nat)
       -> x k
natElim m mz ms Z     = mz
natElim m mz ms (S l) = let rec = natElim m mz ms l 
                        in ms l rec

mZero : Nat -> Nat 
mZero n = n

mSucc : Nat -> (Nat -> Nat) -> Nat -> Nat
mSucc k rec n = S (rec n)

plus : (x : Nat) -> (y : Nat) -> Nat 
plus x y = natElim (\_ => Nat -> Nat) mZero mSucc x y


h3 : (x : Nat -> Type)
  -> (z : x (S Z))
  -> ((a : Nat) -> (b : x (S a)) -> x (S (S a)))
  -> Nat


nat1Elim : (x : Nat -> Type)
        -> (y : x Z) 
        -> (z : x (S Z))
        -> ((a : Nat) -> (b : x (S a)) -> x (S (S a)))
        -> (k : Nat)
        -> x k
nat1Elim m mz m1 ms Z = mz
nat1Elim m mz m1 ms (S l) = let hyp = nat1Elim (\k => m (S k)) m1 (ms Z m1) (\a, rec => ms (S a) rec)
                            in hyp l

nat2Elim : (x : Nat -> Type)
        -> (y : x Z) 
        -> (z : x (S Z))
        -> (zz : x (S (S Z)))
        -> ((a : Nat) -> (b : x (S (S a))) -> x (S (S (S a))))
        -> (k : Nat)
        -> x k
nat2Elim m mz m1 m2 ms Z = mz 
nat2Elim m mz m1 m2 ms (S Z) = m1
nat2Elim m mz m1 m2 ms (S (S l)) = 
        let hyp = nat1Elim (\k => m (S (S k))) m2 (ms Z m2) (\a, rec => ms (S a) rec) 
        in hyp l

Bool : Type
Bool = Fin 2

False : Test.Bool 
False = FZ

True : Test.Bool
True = FS FZ


------------------------------------------------------------------------
listElim : ( x : Type) 
       -> (y : ((z : List x) -> Type))
       -> (z : y []) 
       -> ((b : x) -> (c : List x) -> (d : y c) -> y (b :: c))
       -> (c : List x) 
       -> y c
listElim t y n c [] = n
listElim t y n c (x :: xs) = 
    let rec = listElim t y n c xs
    in c x xs rec


vecElim : ( x : Type) 
       -> (y : ((n : Nat) -> (z : Vect n x) -> Type))
       -> (z : y Z []) 
       -> ((a : Nat) -> (b : x) -> ( c : Vect a x) -> (d : y a c) -> y (S a) (b :: c))
       -> (b : Nat)
       -> (c : Vect b x) 
       -> y b c
vecElim t y n c Z [] = n
vecElim t y n c (S bn) (x :: xs) = 
   let rec = vecElim t y n c bn xs
   in c bn x xs rec

finElim :  (x : ((x : Nat) -> (y : Fin x) -> Type))
        -> ((y : Nat) -> x (S y) FZ)
        -> ((z : Nat) -> (a : Fin z) -> (b : x z a) -> x (S z) (FS a))
        -> (a : Nat)
        -> (b : Fin a) 
        -> x a b
finElim y n c (S bn) FZ = n bn
finElim y n c (S bn) (FS b) = 
        let rec = finElim y n c bn b 
        in c bn b rec

----------------------------------------------------------------------------
Void2   : Type
Void2   = Fin 0

Unit2 : Type
Unit2 = Fin 1

voidElim : (m : Void2 -> Type) -> (v : Void2) -> m v
voidElim m v = 
   let elimF = finElim (natElim (\n => Fin n -> Type) m (\z, fu, fi => Unit2)) (\n => FZ) (\j,a,el => FZ) Z
   in elimF v

listMap : (a : Type) -> (b : Type) -> (f : a -> b) -> List a -> List b 
listMap a b f xs = listElim a (\xs => List b) [] (\x,xs,rec => f x :: rec) xs
   
vecMap : (a : Type) -> (b : Type) -> (n : Nat) -> (f : a -> b) -> Vect n a -> Vect n b 
vecMap a b n f xs = vecElim a (\n, _ => Vect n b) [] (\n,x,xs,rec => f x :: rec) n xs
    

elimF : (n : Nat) 
     -> (fn : Fin n)
     -> (a : Type)
     -> (xs : Vect n a) 
     -> (n' : Nat)
     -> (v : a)
     -> (vs : Vect n' a)
     -> (rec_n' : Fin n' -> a)
     -> (f_succN' : Fin (S n'))
     -> a
elimF n gn a xs n' v vs rec_n' f_succN' = 
      let elimF = finElim (\x, f => a) ?q
      in ?k

-- Projection out of a Vector. Head with a Finite set as the constraint.
vecAt : (a : Type) -> (n : Nat) -> Vect n a -> Fin n -> a
vecAt a n xs fn = 
        let elim = vecElim a (\n, v => Fin n -> a) (\v => voidElim (\v => a) v) 
                             (\n', v, vs, rec_n', f_succN' => 
                              ?p
                             )
        in ?body


listHead : (a : Type) -> List a -> Maybe a 
listHead a xs = 
        let elim = listElim a (\l => Maybe a) Nothing (\x, xs, rec => Just x) xs
        in elim

listTail : (a : Type) -> List a -> List a 
listTail a xs =
        let elim = listElim a (\l => List a) [] (\x,xs,rec => xs) xs 
        in elim

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

{-
||| Construct a list with `n` copies of `x`
||| @ n how many copies
||| @ x the element to replicate
replicate : (n : Nat) -> (x : a) -> List a
replicate Z     x = []
replicate (S n) x = x :: replicate n x
-}

listReplicate  : (a : Type) -> (n : Nat) -> (x : a) -> List a 
listReplicate a n x = 
        let elim = natElim (\n => a -> List a) (\x => []) (\n,rec,x => x :: rec x) n x
        in elim


{-
||| Compute the length of a list.
|||
||| Runs in linear time
length : List a -> Nat
length []      = Z
length (x::xs) = S (length xs)
-}

listLength : (a : Type) -> List a -> Nat
listLength a xs = 
        let elim = listElim a (\l => Nat) Z (\x,xs,rec => S rec) xs 
        in elim

{-
||| Take the first `n` elements of `xs`
|||
||| If there are not enough elements, return the whole list.
||| @ n how many elements to take
||| @ xs the list to take them from
take : (n : Nat) -> (xs : List a) -> List a
take Z     xs      = []
take (S n) []      = []
take (S n) (x::xs) = x :: take n xs
-}

listTake : (a : Type) -> (n : Nat) -> (xs : List a) -> List a 
listTake a n xs = 
        let elim = natElim (\l => List a -> List a) 
                    (\xs => []) 
                    (\sn,rec,xs => listElim a (\l => List a) 
                           [] 
                           (\x',xs',rec' => x' :: rec xs' ) 
                      xs) 
                   n xs
        in elim

{-
||| Drop the first `n` elements of `xs`
|||
||| If there are not enough elements, return the empty list.
||| @ n how many elements to drop
||| @ xs the list to drop them from
drop : (n : Nat) -> (xs : List a) -> List a
drop Z     xs      = xs
drop (S n) []      = []
drop (S n) (x::xs) = drop n xs
-}

listDrop : (a : Type) -> (n : Nat) -> (xs : List a) -> List a 
listDrop a n xs = 
        let elim = natElim (\n => List a -> List a) 
                        (\xs => xs) 
                        (\sn,rec,xs => 
                             listElim a (\l => List a) 
                                []
                                (\x',xs',rec' => rec xs')
                              xs )
                        n xs
        in elim