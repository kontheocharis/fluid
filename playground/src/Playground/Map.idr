module Map

import Data.Nat
import Data.Fin 
import Data.Vect

import RefacPrelude

listMap : (a : Type) -> (b : Type) -> (f : a -> b) -> List a -> List b 
listMap a b f xs = listElim a (\xs => List b) [] (\x,xs,rec => f x :: rec) xs
   
vectToList : Vect n a -> List a 
vectToList xs = toList xs

-- change input parameter to vect, introduce fresh bound. 
-- gives type error: unifying vect with list.
-- listMap2 : (a : Type) -> (b : Type) -> (f : a -> b) -> (n : Nat) -> Vect n a -> List b 
-- listMap2 a b f n xs = listElim a (\xs => List b) [] (\x,xs,rec => f x :: rec) xs


-- change all occurrences of bounded xs with a converter wrapper.
listMap3 : (a : Type) -> (b : Type) -> (f : a -> b) -> (n : Nat) -> Vect n a -> List b 
listMap3 a b f n xs = listElim a (\xs => List b) [] (\x,xs,rec => f x :: rec) (vectToList xs)


listMap4 : (a : Type) -> (b : Type) -> (f : a -> b) -> (n : Nat) -> Vect n a -> List b 
listMap4 a b f n xs = vecElim a (\n,xs => List b) [] (\n,x,xs,rec => f x :: rec) n xs



listMap5' : (a : Type)
         -> (b : Type)
         -> (f : a -> b)
         -> (n : Nat)
         -> (x : a)
         -> (xs : Vect n a)
         -> (rec : (m ** Vect m b))
         -> (m  ** Vect m b)
listMap5' a b f n x xs rec = 
        let elim = sigElim Nat (\m => Vect m b) (\a => (m : Nat ** Vect m b)) 
                        (\m,vm => (S m ** f x :: vm))
                        rec
                        
        in elim


mapFV : (a : Type) -> (b : Type) -> (f : a -> b) 
     -> (n : Nat) -> Vect n a 
     -> (m ** Vect m b)
mapFV a b f Z [] = (0 ** [])
mapFV a b f (S n) (x::xs) = 
        case mapFV a b f n xs of 
                (m' ** vm') => (S m' ** f x :: vm')
-- mapFV a b f n (x:xs) = ?mapV

-- change the output type.
listMap5 : (a : Type) -> (b : Type) -> (f : a -> b) 
        -> (n : Nat) -> Vect n a 
        -> (m ** Vect m b) 
listMap5 a b f n xs = 
        let elim = vecElim a (\n,xs => (m ** Vect m b)) 
                             (Z ** [])
                             (\n,x,xs,rec => sigElim Nat (\m => Vect m b) 
                                                         (\a => (m : Nat ** Vect m b)) 
                                                         (\m,vm => (S m ** f x :: vm))
                                                         rec)
                             n 
                             xs
        in elim

-- remove DP and unify.
listMap6 : (a : Type) -> (b : Type) -> (f : a -> b) 
        -> (n : Nat) -> Vect n a 
        -> Vect n b
listMap6 a b f n xs = 
        let elim = vecElim a (\n,xs => Vect n b) 
                             []
                             (\n,x,xs,rec => f x :: rec)
                             n 
                             xs
        in elim


listMap7' : (n : Nat)
         -> (a : Type)
         -> (b : Type)
         -> (f : a -> b)
         -> (n' : Nat)
         -> (x : a)
         -> (xs : Vect n' a)
         -> (rec : (m : Nat ** (n' = m, Vect m b)))
         -> (m : Nat)
         -> (vm : (n' = m, Vect m b))
------------------------------
        -> (S n' = S m, Vect (S m) b)
listMap7' n a b f n' x xs rec m vm = 
    let elim = eqElim Nat (\y, z, prf => S y = S z) (\z => Refl) n' m (fst vm) 
    in (elim, (f x :: (snd vm)))


-- Q: How do we know how to unify?
-- could add a returning proof that n = m?
listMap7 : (a : Type) -> (b : Type) -> (f : a -> b) 
        -> (n : Nat) -> Vect n a 
        -> (m ** (n = m, Vect m b))
listMap7 a b f n xs = 
        let elim = vecElim a (\n,xs => (m ** (n = m, Vect m b))) -- (m ** (Refl, Vect m b)))
                            (Z ** (Refl, []))
                         --   ?k
                             (\n',x,xs,rec => -- ?pp )
                                sigElim Nat 
                                    (\m => (n' = m, Vect m b))
                                    (\a => (m : Nat ** (S n' = m, Vect m b)))
                                    (\m,vm => 
                                        (S m ** 
                                          --  listMap7' n a b f n' x xs rec m vm
                                          (eqElim Nat (\y, z, prf => S y = S z) (\z => Refl) n' m (fst vm), f x :: (snd vm))
                                        )) -- f x :: vm))
                                    rec)
                             n 
                             xs 
        in elim



vecMap : (a : Type) -> (b : Type) -> (n : Nat) -> (f : a -> b) -> Vect n a -> Vect n b 
vecMap a b n f xs = vecElim a (\n, _ => Vect n b) [] (\n,x,xs,rec => f x :: rec) n xs
    

