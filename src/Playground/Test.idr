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


listHead : (a : Type) -> List a -> Maybe a 
listHead a xs = 
        let elim = listElim a (\l => Maybe a) Nothing (\x, xs, rec => Just x) xs
        in elim

{-
||| Only the first element of the vector
|||
||| ```idris example
||| head [1,2,3,4]
||| ```
head : Vect (S len) elem -> elem
head (x::xs) = x
-}

-- at : forall (x :: *) (y :: Nat) (z :: Vec x y) (a :: Fin y) . x

-- vec projection using finite sets
-- defined using standard recursion
at : (t : Type) -> (y : Nat) -> (z : Vect y t) -> (a : Fin y) -> t
at t Z [] a = 
     let elim =  voidElim (\f => t) a
     in elim
at t (S n) (v::vs) FZ = v
at t (S n) (v::vs) (FS fn) = at t n vs fn

{-
eqElim : forall (x :: *)
       (y :: forall (y :: x) (z :: x) (a :: Eq x y z) . *)
       (z :: forall z :: x . y z z (Refl x z))
       (a :: x)
       (b :: x)
       (c :: Eq x a b) .
y a b c
-}

eqElim : (x : Type)
      -> (y : ((y : x) -> (z : x) -> (a : y = z) -> Type))
      -> (z : ((z : x) -> y z z Refl))
      -> (a : x)
      -> (b : x) 
      -> (c : a = b) 
      -> y a b c 
eqElim t y z a a Refl = z a


vecAt : (t : Type) -> (y : Nat) -> (z : Vect y t) -> (a : Fin y) -> t 
vecAt t y z a = 
        let elimN = vecElim t (\n, vs => Fin n -> t) 
                          (\f => voidElim (\f' => t) f) -- empty case
                          (\n', v, vs, rec, f => 
                                 finElim (\n,f => n = (S n') -> t) 
                                         (\n,e => v) 
                                         (\n,fn,rec',e => 
                                               ---  ?fff
                                               rec (eqElim Nat 
                                                           (\y,z,e => Fin y -> Fin z) 
                                                           (\z, fn2 => fn2)
                                                           n n'
                                                           (cong pred e) fn))
                                         (S n')
                                         f 
                                         Refl)

                             -- cons case
        in elimN y z a

vecHead : (a : Type) -> (n : Nat) -> Vect (S n) a -> a 
vecHead a n v = vecAt a (S n) v FZ



listTail : (a : Type) -> List a -> List a 
listTail a xs =
        let elim = listElim a (\l => List a) [] (\x,xs,rec => xs) xs 
        in elim

-- with Eliminators we cannot discard the empty vector case, so we cannot use
-- vecTail, below. THis means we need another helper function, allowing us
-- to pattern match on []. 
-- We pass a proof as arugment, to allow us to return a vector that is at least 1 in length.

-- vecTail' : (a : Type) -> (n : Nat) -> Vect n a -> (prf : n = (S m)) -> Vect m a
-- vecTail' a Z [] Refl impossible
-- vecTail' a (S n) (x::xs) Refl = xs

apply : (a : Type) -> (b : Type) -> (a = b) -> a -> b

Not : Type -> Type 
Not t = t -> Fin 0

p0isNot1 : (y : Z = (S Z)) -> Fin 0
p0isNot1 y = 
        let elim = natElim (\n => Type) Void2 (\n,t => Fin 1)
            con  = cong (natElim (\n => Type) Void2 (\n,t => Fin 1)) (sym y)
        in Test.apply (Fin 1) Void2 con FZ


p0IsNoSucc : (x : Nat) -> (y : 0 = (S x)) -> Fin 0 
p0IsNoSucc Z     y = p0isNot1 y
p0IsNoSucc (S n) y = p0IsNoSucc n (cong pred y) 


helpElim : (a : Type)
        -> (n : Nat)
        -> (v : Vect n a)
        -> (a' : Nat)
        -> (x : a)
        -> (xs : Vect a' a)
        -> (rec : (m : Nat) -> a' = S m -> Vect m a)
        -> (m : Nat)
        -> (p : S a' = S m)
        -> Vect m a 
helpElim a n v a' x xs rec m p = 
        let elim = eqElim Nat (\n',m',p => Vect n' a -> Vect m' a) (\z,zv => zv) a' m (cong pred p) xs
        in elim

vecTail' : (a : Type) -> (n : Nat) -> Vect n a -> (m : Nat) -> (prf : n = (S m)) -> Vect m a 
vecTail' a n v m p = 
        let elimE = eqElim Nat (\n,m,p => Vect n a -> Vect m a) (\z,zv => zv) n m ?pp
            elim = vecElim a (\n,v => (m : Nat) -> n = (S m) -> Vect m a) 
                             (\m,absPrf => voidElim (\f => Vect m a) (p0IsNoSucc m absPrf))  -- case where we have a proof 0 = S m 
                             (\a',x,xs,rec,m',p' =>  -- we need to effectively case on cong pred p  
                                                  -- meaning an eqElim...
                                -- helpElim a n v a' x xs rec m' p'
                                eqElim Nat 
                                       (\n',m',p => Vect n' a -> Vect m' a) 
                                       (\z,zv => zv) 
                                       a' m' 
                                       (cong pred p') xs
                             )

        in elim n v m p

vecTail : (a : Type) -> (n : Nat) -> Vect (S n) a -> Vect n a 
vecTail a n v = vecTail' a (S n) v n Refl


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


-- vecAppend' : (a : Type) -> (n : Nat) -> Vect n a -> (m : Nat) -> Vect m a -> Vect (n+m) a
-- vecAppend' a Z [] m v2 = v2
-- vecAppend' a (S n) (x :: xs) m v2 = x :: (vecAppend' a n xs m v2)

vecAppend : (a : Type) -> (n : Nat) -> Vect n a -> (m : Nat) -> Vect m a -> Vect (n+m) a
vecAppend a n v1 m v2 = 
        let elim = vecElim a (\n,ve => (m:Nat) -> Vect m a -> Vect (n+m) a) 
                              -- empty vec case
                              (\n,v2' => v2')
                              -- cons case 
                              (\t,x,xs,rec,m',v2' => x :: rec m' v2')
        in elim n v1 m v2

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

-- vecReplicate : (a : Type) -> (n : Nat) -> (x : a) -> Vect n a 
-- vecReplicate a Z x = []
-- vecReplicate a (S n) x = x :: vecReplicate a n x

vecReplicate : (a : Type) -> (n : Nat) -> (x : a) -> Vect n a 
vecReplicate a n x = 
        let elim = natElim (\n => a -> Vect n a) 
                                (\x => []) 
                                (\n,rec,x => x :: rec x ) n x
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

vecLength : (a : Type) -> (n: Nat) -> Vect n a -> Nat 
vecLength a n v = 
        let elim = vecElim a (\n,v => Nat) Z (\n,x,xs,rec => S rec) n v
        in elim -- kind of pointless, as we need to make n explicit.

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

-- vecTake : (a : Type) -> (n : Nat) -> (m : Nat) -> (xs : Vect (n+m) a) -> Vect m a 
-- vecTake a Z m xs = xs 
-- vecTake a (S n) m (x::xs) = vecTake a n m 

{-
p0isNot1 : (y : Z = (S Z)) -> Fin 0
p0isNot1 y = 
        let elim = natElim (\n => Type) Void2 (\n,t => Fin 1)
            con  = cong (natElim (\n => Type) Void2 (\n,t => Fin 1)) (sym y)
        in Test.apply (Fin 1) Void2 con FZ
-}

vecLengthEq : (Vect a n = Vect b n) -> a = b 
vecLengthEq Refl = Refl

vecLengthEq2 : (a : Type) -> (n1 : Nat) -> (n2 : Nat) -> (Vect n1 a = Vect n2 a) -> n1 = n2
vecLengthEq2 a n1 n2 prf = 
        let elim = eqElim (Vect n1 a) (\y,z,prf => n1 = n2) (\a => ?t )
        in ?bo


v0IsNo1 : (a : Type) -> (Vect 0 a = Vect 1 a) -> Fin 0 
v0IsNo1 a prf = p0isNot1 (vecLengthEq prf)

vIsNoSucc : (m : Nat) -> (y : Vect m a = (Vect (S m) a)) -> Fin 0 
vIsNoSucc Z prf = ?h
vIsNoSucc (S n) prf = ?h2

takeHelper :    (m : Nat)
          ->    (n : Nat)
          ->    (a : Type)
          ->    (m' : Nat)
          ->    (rec : Vect (m' + m) a -> Vect m a)
          ->    (xs : Vect (S (m' + m)) a)
          ->     Vect m a
takeHelper m n a m' rec xs = 
        let elimV = voidElim (\v => Vect m a) ?v
            elim = vecElim a (\n,vec => Vect m a) 
                        elimV 
                        (\a,x,xs,rec => rec)
        in ?body2




vecTake : (a : Type) -> (n : Nat) -> (m : Nat) -> (xs : Vect (n+m) a) -> Vect m a
vecTake a n m xs = 
        let elim = natElim (\n => Vect (n+m) a -> Vect m a) 
                                -- Z case
                                (\xs => xs)
                                (\m',rec,xs => ?g)
        in ?body

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