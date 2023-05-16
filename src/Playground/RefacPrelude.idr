module RefacPrelude

import Data.Nat
import Data.Fin
import Data.Vect

public export
natElim : (x : Nat -> Type) 
       -> (y : x Z)
       -> ((z : Nat) -> (a : x z) -> x (S z))
       -> (k : Nat)
       -> x k
natElim m mz ms Z     = mz
natElim m mz ms (S l) = let rec = natElim m mz ms l 
                        in ms l rec

public export
mZero : Nat -> Nat 
mZero n = n

public export
mSucc : Nat -> (Nat -> Nat) -> Nat -> Nat
mSucc k rec n = S (rec n)

public export
plus : (x : Nat) -> (y : Nat) -> Nat 
plus x y = natElim (\_ => Nat -> Nat) mZero mSucc x y


public export
h3 : (x : Nat -> Type)
  -> (z : x (S Z))
  -> ((a : Nat) -> (b : x (S a)) -> x (S (S a)))
  -> Nat

public export
nat1Elim : (x : Nat -> Type)
        -> (y : x Z) 
        -> (z : x (S Z))
        -> ((a : Nat) -> (b : x (S a)) -> x (S (S a)))
        -> (k : Nat)
        -> x k
nat1Elim m mz m1 ms Z = mz
nat1Elim m mz m1 ms (S l) = let hyp = nat1Elim (\k => m (S k)) m1 (ms Z m1) (\a, rec => ms (S a) rec)
                            in hyp l

public export
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

public export
Bool : Type
Bool = Fin 2

public export
False : RefacPrelude.Bool 
False = FZ

public export
True : RefacPrelude.Bool
True = FS FZ

public export
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

public export
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

public export
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

public export
Void2   : Type
Void2   = Fin 0

public export
Unit2 : Type
Unit2 = Fin 1

public export
voidElim : (m : Void2 -> Type) -> (v : Void2) -> m v
voidElim m v = 
   let elimF = finElim (natElim (\n => Fin n -> Type) m (\z, fu, fi => Unit2)) (\n => FZ) (\j,a,el => FZ) Z
   in elimF v

public export
sigElim  : (a : Type)
        -> (f : a -> Type) 
        -> (x : (y : a  ** f y) -> Type)
        -> ((w : a) -> (g : f w) -> x (w ** g))
        -> (k : (y : a ** f y))
        -> x k 
sigElim a f x w (y ** g) = w y g


public export 
eqElim : (x : Type)
      -> (y : ((y : x) -> (z : x) -> (a : y = z) -> Type))
      -> (z : ((z : x) -> y z z Refl))
      -> (a : x)
      -> (b : x) 
      -> (c : a = b) 
      -> y a b c 
eqElim t y z a a Refl = z a

public export
fstS : (n ** Vect n Nat) -> Nat 
fstS s = sigElim Nat 
                (\n => Vect n Nat)   
                (\s => Nat)
                (\w, g =>  w)
                s 