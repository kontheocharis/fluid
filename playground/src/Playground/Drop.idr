module Drop 

import Data.Nat
import Data.Fin 
import Data.Vect

import RefacPrelude

vectToList : Vect n a -> List a 
vectToList xs = toList xs


{-
listDrop : (a : Type) -> (n : Nat) -> List a -> List a 
listDrop a Z xs = xs
listDrop a (S n') [] = []
listDrop a (S n') (x::xs) = listDrop a n' xs
-}


listDrop : (a : Type) -> (n : Nat) -> List a -> List a 
listDrop a n xs = 
    natElim (\n => List a -> List a) 
                       (\l => l) 
                       (\x, rec, xs => 
                            listElim a
                                (\l => List a) 
                                []
                                (\x', xs', rec' => rec xs')
                                xs
                       )
                       n
                       xs

-------------------------------------------------------------------------------
-- Convert input list to vector, introducing m

-- ddrop' Z xs = (length xs ** xs)
-- ddrop'' Z xs = rewrite lengthCorrect xs in (length xs ** xs)

{-
drop1 : (n : Nat) -> (m : Nat) -> Vect m a -> List a
drop1 Z m xs = toList xs
drop1 (S n') Z [] = []
drop1 (S n') (S m') (x :: xs) = drop1 n' m' xs
-}

listDrop1 : (a : Type) -> (n : Nat) -> (m : Nat) -> Vect m a -> List a
listDrop1 a n m xs = 
    natElim (\n => (m : Nat) -> Vect m a -> List a)
            (\m, v => toList v)
            (\m, rec, n, v => vecElim a (\n, v => List a) [] (\n,x',xs', rec' => rec n xs') n v ) n m xs

-- Convert output list to vector, introducing ∑-type
{-
drop2 : (n : Nat) -> (m : Nat) -> Vect m a -> (k : Nat ** Vect k a) 
drop2 Z m xs = (m ** xs) -- how we get from `toList xs` to this is a mystery.
                         -- Perhaps it is a matter of ordering the refactorings.
                         -- It could also be a matter of library knowledge.
                         -- (i.e. if we know that toList is a function that
                         -- changes List -> Vect, then we know enough to remove
                         -- it.)
drop2 (S n') Z [] = (Z ** [])
drop2 (S n') (S m') (x :: xs) = drop2 n' m' xs
-}

listDrop2 : (a : Type) -> (n : Nat) -> (m : Nat) -> Vect m a -> (k : Nat ** Vect k a) 
listDrop2 a n m xs = 
    natElim (\n => (m : Nat) -> Vect m a -> (k : Nat ** Vect k a))
            (\m, v => (m ** v))
            (\m, rec, n, v => vecElim a (\n, v => (k : Nat ** Vect k a)) (Z ** []) (\n,x',xs', rec' => rec n xs') n v ) n m xs
    


-------------------------------------------------------------------------------
-- Restrict domain of drop


drop3 : (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m)
     -> (k : Nat ** Vect k a)
drop3 Z m xs p = (m ** xs)
drop3 (S n') Z [] p = (Z ** []) -- technically impossible
                                -- but if we don't pattern match...
drop3 (S n') (S m') (x :: xs) (LTESucc p') = drop3 n' m' xs p'
                                -- we need to pass something to the recursive
                                -- call, so we case split
                                -- here, we have only one possibility b/c
                                -- of the arguments, and it becomes obvious what
                                -- to plug in


vecHelp :  (n : Nat)
        -> (p : LTE n m)
        -> (a : Type)
        -> (xs : Vect m a)
        -> (elim : (l : Nat) -> (r : Nat) -> LTE l r -> (k : Nat ** Vect k a))
        -> (elimV : (b : Nat) -> Vect b a -> LTE b m -> (k : Nat ** Vect k a))
        -> (z : Nat)
        -> (rec : (m : Nat) -> Vect m a -> LTE z m -> (k : Nat ** Vect k a))
        -> (m : Nat)
        -> (v : Vect m a)
        -> (p' : LTE (S z) m)
------------------------------
        -> (k : Nat ** Vect k a)
vecHelp n p a xs elim elimV z rec m v p' = 
    let elim = lteElim (\l, r, p => (k : Nat ** Vect k a)) 
                       (\n => (Z ** [])) 
                       (\le, ri, p, rec' => rec') 
        elimV = vecElim a (\n, v => (p : LTE n m) -> (k : Nat ** Vect k a)) 
                          (\p0 => (Z ** [])) 
                          (\lxs, x, xs, rec', p'' => elim (S lxs) m p''  ) n ?hole77
    in ?vh

vecHelp2 :  (n : Nat)
        -> (p : LTE n m)
        -> (a : Type)
        -> (xs : Vect m a)
        -> (elim : (l : Nat) -> (r : Nat) -> LTE l r -> (k : Nat ** Vect k a))
        -> (elimV : (b : Nat) -> Vect b a -> LTE b m -> (k : Nat ** Vect k a))
        -> (z : Nat)
        -> (rec : (m : Nat) -> Vect m a -> LTE z m -> (k : Nat ** Vect k a))
        -> (m : Nat)
        -> (v : Vect m a)
        -> (p' : LTE (S z) m)
------------------------------
        -> (k : Nat ** Vect k a)
vecHelp2 n p a [] elim elimV z rev m v p' =       (Z ** [])
vecHelp2 n p a [] elim elimV z rev Z v p' impossible
vecHelp2 n p a (x::xs) elim elimV z rev (S m') v (LTESucc p') =  ?vH1 


vHelp : (a : Type) 
    -> ( m : Nat )
    -> (n : Nat)
    -> (elimL : (l : Nat) -> (r : Nat) -> LTE l r -> (k : Nat ** Vect k a))
    -> (a2 : Nat)
    -> (x : a)
    -> (xs : Vect a2 a)
    -> (rec : LTE n a2 -> (k : Nat ** Vect k a))
    -> (p : LTE n (S a2))
------------------------------
    -> (k : Nat ** Vect k a)
vHelp a m n elimL a2 x xs rec p = 
    let elimL = lteElim (\l, r, p => (k : Nat ** Vect k a)) (\n => (Z ** [])) (\le, ri, p', rec' => ?hole22 ) 
    in ?body

-- this gets the wrong behaviour. Possibly because the use of rec is not correct in the
-- LTE eliminator.
-- The ordering of elimninating probably matters. 
-- We want to recurse on the tail of the list, not the inductive step of the proof. 
listDrop3 : (a : Type) -> (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m) -> (k : Nat ** Vect k a) 
listDrop3 a n m xs p = 
    let elimL = lteElim (\l, r, p => (k : Nat ** Vect k a)) (\n => ?hole99) (\le, ri, p, rec => rec) 
        elimV = vecElim a (\m, v => (p : LTE n m) -> (k : Nat ** Vect k a)) (\p0 => (Z ** [])) (\a2, x, xs, rec, p => lteElim (\l, r, p => (k : Nat ** Vect k a)) (\n => (a2 ** xs)) (\le, ri, p, rec => rec) n (S a2) p) 
        elimN2 = natElim (\n' => Vect m a -> LTE n m -> (k : Nat ** Vect k a))
                         (\vm, p0 => (Z ** []))
                         (\m', rec, vnm', psm' => elimV m vnm' psm')
        elimN = natElim (\n => (m : Nat)  -> Vect m a -> LTE n m -> (k : Nat ** Vect k a))
                        (\m,v,p => (m ** v))
                        (\z, rec, m', v, p' =>  elimN2 m xs p) -- vecElim a (\n, v => (p : LTE n m) -> (k : Nat ** Vect k a)) (\p0 => (Z ** [])) (\a, x, xs, rec, p => elim ) m v p' )
    in elimN n m xs p
 -- vecElim a (\n, v, p => LTE n m -> (k : Nat ** Vect k a)) (\p => Z ** []) (\n,x',xs', p' , rec' => ?hole) n v ) n m xs


-- drop3 (S n') (S m') (x :: xs) (LTESucc p') = drop3 n' m' xs p'

--------------------------------------------------------------------------------------------

elimL : (z' : Nat)
   -> (z : Nat)
   -> (p'' : LTE (S z) (S z'))
   -> (a : Type)
   -> (v' : Vect (S z') a)
   -> (rec' : Vect z' a -> LTE (S z) z' -> (k : Nat ** Vect k a))
   -> (n : Nat)
   -> (m : Nat)
   -> (xs : Vect m a)
   -> (p : LTE z m)
   -> (rec : (m : Nat) -> Vect m a -> LTE z m -> (k : Nat ** Vect k a))
   -> (m' : Nat)
   -> (v : Vect m' a)
   -> (p' : LTE (S z) m')
   -> (a' : Nat)
   -> (x' : a)
   -> (xs' : Vect a' a)
   -> (rec'' : LTE (S z) (S m') -> (k : Nat ** Vect k a))
   -> (p''' : LTE (S z) (S m'))
   -> (prf : z = (S z'))
------------------------------
   -> (k : Nat ** Vect k a)
elimL z' z p'' a v' rec' n m xs p rec m' v p' a' x' xs' rec'' p''' prf  = 
    let elimL' = lteElim (\l, r, p => (k : Nat ** Vect k a)) (\n => (Z ** [])) (\le, ri, p'''', rec''' => rec a' xs'  ?hole4) z a' -- rec a' xs' (lteSuccLeft p''')) -- rec m' v (lteSuccLeft p') ) -- rec'' p''') 
    in ?body3 -- elimL' n m p'''

elimV :  ( m' : Nat)
   -> (z : Nat)
   -> (p' : LTE (S z) m')
   -> (a : Type)
   -> (v : Vect m' a)
   -> (rec : (m : Nat) -> Vect m a -> LTE z m -> (k : Nat ** Vect k a))
   -> (m : Nat)
   -> (p : LTE z m)
   -> (xs : Vect m a)
   -> (n : Nat)
   -> (z' : Nat)
   -> (rec' : Vect z' a -> LTE (S z) z' -> (k : Nat ** Vect k a))
   -> (v' : Vect (S z') a)
   -> (p'' : LTE (S z) (S z'))
------------------------------
    -> (k : Nat ** Vect k a)
elimV m' z p' a v rec m p xs n z' rec' v' p'' = 
    let elimV' = vecElim a (\m, v => (p : LTE (S z) (S m')) -> (k : Nat ** Vect k a)) (\p0 => (Z ** [])) (\m', x', xs', rec'',p''' => ?hole3) -- elimL z' n p'' a v' rec' m p xs z rec m' v p' a' x' xs' rec'' p''') -- (\p0 => (Z ** [])) (\a, x, xs, rec, p => ?hole99) 
    in ?body2 -- elimV' m' v p


elimN2 : (m : Nat)
      -> (n : Nat)
      -> (a : Type)
      -> (xs : Vect m a)
      -> (z : Nat)
      -> (p : LTE z m)
      -> (rec : (m : Nat) -> Vect m a -> LTE z m -> (k : Nat ** Vect k a))
      -> (m' : Nat)
      -> (v : Vect m' a)
      -> (p' : LTE (S z) m')
------------------------------
      -> (k : Nat ** Vect k a)
elimN2 m n a xs z p rec m' v p' =
    let elimN2' = natElim (\m => Vect m a -> LTE (S z) m -> (k : Nat ** Vect k a))
                          (\vm, p0 => (Z ** []))
                          (\z', rec', v', p'' => ?hole2) -- elimV m' z p' a v rec m xs n p z' rec' v' p'')
    in ?body55 -- elimN2' m xs p'


listDrop4 : (a : Type) -> (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m) -> (k : Nat ** Vect k a) 
listDrop4 a n m xs p = 
    let -- elimL = lteElim (\l, r, p => (k : Nat ** Vect k a)) (\n => (Z ** [])) (\le, ri, p, rec => rec) 
        -- elimV = vecElim a (\m, v => (p : LTE n m) -> (k : Nat ** Vect k a)) (\p0 => (Z ** [])) (\a, x, xs, rec, p => ?hole) -- elimL n (S a) p) 
        -- elimN2 = natElim (\n' => Vect m a -> LTE n m -> (k : Nat ** Vect k a))
        --                 (\vm, p0 => (Z ** []))
        --                 (\m', rec, vnm', psm' => elimV m vnm' psm')
        elimN = natElim (\z => (m : Nat)  -> Vect m a -> LTE z m -> (k : Nat ** Vect k a))
                        (\m,v,p => (m ** v))
                        (\z, rec, m, v, p' => ?hole1) -- elimN2 m n a xs z p rec m' v p') -- elimN2 m xs p) -- vecElim a (\n, v => (p : LTE n m) -> (k : Nat ** Vect k a)) (\p0 => (Z ** [])) (\a, x, xs, rec, p => elim ) m v p' )
    in elimN n m xs p



listDrop5 : (a : Type) -> (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m) -> (k : Nat ** Vect k a) 
listDrop5 a n m xs p = 
    let elimN = natElim (\n => (m : Nat)  -> Vect m a -> LTE n m -> (k : Nat ** Vect k a))
                        (\m,v,p => (m ** v))
                        (\z, rec, m', v, p' =>  natElim (\n' => Vect m a -> LTE n m -> (k : Nat ** Vect k a))
                         (\vm, p0 => (Z ** []))
                         (\m', rec, vnm', psm' => vecElim a (\m, v => (p : LTE n m) -> (k : Nat ** Vect k a)) (\p0 => (Z ** [])) (\a2, x, xs, rec, p => lteElim (\l, r, p => (k : Nat ** Vect k a)) (\n => (a2 ** xs)) (\le, ri, p, rec => rec) n (S a2) p) m vnm' psm') m xs p) -- vecElim a (\n, v => (p : LTE n m) -> (k : Nat ** Vect k a)) (\p0 => (Z ** [])) (\a, x, xs, rec, p => elim ) m v p' )
    in elimN n m xs p








-----------------------------------------------------------------------------

















