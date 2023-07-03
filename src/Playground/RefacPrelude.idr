module RefacPrelude

import Data.Nat
import Data.Fin
import Data.Vect
import Decidable.Equality

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
lteElim :   (x : (l : Nat) -> (r : Nat) -> LTE l r -> Type)
       ->   (z : (r : Nat) -> x Z r LTEZero)
       ->   (nz : ((left : Nat) -> (right : Nat) -> (l : LTE left right) -> (x left right l) ->  (x (S left) (S right) (LTESucc l))))
       ->   (l : Nat) 
       ->   (r : Nat)
       ->   (lte : LTE l r)
       ->  x l r lte
lteElim x z nz Z ri (LTEZero) = z ri
lteElim x z nz (S le) (S ri) (LTESucc l) = 
        let rec = lteElim x z nz le ri l  
        in nz le ri l rec
       -- let rec = lteElim x z nz le ri l  
       --  in nz le ri l rec


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

U : Unit2
U = FZ

public export
Not2 : Type -> Type 
Not2 = (\a => a -> Void2)

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


-- Leibniz prinicple (look at the type signature)
public export
leibniz : (a : Type) -> (b : Type) -> (f : a -> b) -> (x : a) -> (y : a) -> x = y ->  (f x) = (f y)
leibniz =
  ( \ a, b, f => eqElim a
                 (\ x, y, eq_x_y => (f x) = (f y))
                 (\ x => Refl  ))
  

-- apply an equality proof on two types
public export 
apply2 : (a : Type) -> (b : Type) -> (p : a = b) -> a -> b
apply2 =
  eqElim Type (\ a, b, _ => a -> b) (\ _ , x => x)


-- proof that 1 is not 0
public export 
p1IsNot0 : (S Z) = Z -> Void2
p1IsNot0 = (\ p => apply2 Unit2 Void2
                   (leibniz Nat Type
                         (natElim (\ _ => Type) Void2 (\ _, _ => Unit2))
                         1 0 p)
                U)
--  :: Not (Eq Nat 1 0)

-- proof that S n is not 0
public export 
pSnIsNot0 : (n : Nat) -> (S n) = Z -> Void2
pSnIsNot0 = (\ n, p => apply2 Unit2 Void2
                   (leibniz Nat Type
                         (natElim (\ _ => Type) Void2 (\ _, _ => Unit2))
                         (S n) 0 p)
                U)


{-
public export
succNotLTEzero : (m : Nat) -> (S m `LTE` Z) -> Void2
succNotLTEzero m p = 
  let   ltEl = lteElim (\l,r,p => Type) 
                       (\r => Void2)
                       (\l,r,p,v => Unit) -- (S m) Z p 
        le = leibniz (LTE (S m) Z) Type (ltEl (S m) Z) p p Refl -- (ltEl (S m) Z) ?l ))
        help = apply2 Unit Void2
  in help ()
-}

-- public export
--NoConfusion : Nat -> Nat -> Type 
--NoConfusion Z Z = Z = Z 
--NoConfusion (S n) (S m) = n = m 
--NoConfusion _ _ = Void2

public export
NoConfusion : Nat -> Nat -> Type 
NoConfusion x y = 
 natElim (\x => Nat -> Type) 
                   (\y => natElim (\y => Type) 
                                  (Z = Z)
                                  (\m, t => Void2)
                                  y )
                   (\n, hyp, sm => natElim (\y => Type) 
                                           Void2 
                                           (\m, t => n = m)
                                           sm ) x y 


--public export
--noConf : (x , y : Nat) -> x = y -> NoConfusion x y 
--noConf Z Z p = Refl
--noConf (S n) (S n) Refl = Refl 

public export 
noConf : (x, y : Nat) -> x = y -> NoConfusion x y 
noConf x y p = 
  natElim (\x => (y : Nat) -> x = y -> NoConfusion x y)
                    (\y, p0ey => natElim (\y => Z = y -> NoConfusion Z y) 
                                         (\p => Refl) 
                                         (\z,hyp,p => pSnIsNot0 z (sym p)) y p0ey)
                    (\sx, hyp, y, p => natElim (\y => (S sx) = y -> NoConfusion (S sx) y)
                                               (\p => pSnIsNot0 sx p )
                                               (\z, hyp, p => cong pred p) y p) x y p 
  

public export
apply3 : (a : Type) -> (x,y : a) -> (p : a -> Type) -> x = y -> p x -> p y
apply3 a x x p Refl px = px

public export
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

public export 
fromLteSucc2 : (n,m : Nat) -> LTE (S n) (S m) -> LTE n m
fromLteSucc2 n m p  = lteElim (\k,l,_ => k = S n -> l = S m -> LTE n m)
                         (\_,e,_ => voidElim (\_ => LTE n m) (noConf Z (S n) e))
                         (\k,l,e,_,x,y => apply3 Nat k n (\n => LTE n m) (noConf (S k) (S n) x) (apply3 Nat l m (\m => LTE k m) (noConf (S l) (S m) y) e))
                      (S n) (S m) p Refl Refl 

public export 
lengthL : (a : Type) -> (xs : List a) -> Nat 
lengthL a xs = listElim a (\xs => Nat) 
                          Z 
                          (\x, xs, rec => RefacPrelude.plus 1 rec) xs
        
public export 
vectToList : ( a : Type ) -> ( n : Nat ) -> ( xs : Vect n a ) -> List a 
vectToList a n s = 
        vecElim a 
                (\n, xs => List a)
                []
                (\n, x, xs, rec => x ::  rec) n s 