module Drop2 

import Data.Nat
import Data.Fin 
import Data.Vect

import RefacPrelude

vectToList : Vect n a -> List a 
vectToList xs = toList xs


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

-------------------------------------------------------------------------------------------------------
drop4PE : (a : Type) -> (n' : Nat) -> (xsTM : Nat) -> Vect xsTM a -> (pSN'SSxsTM : LTE (S n') (S xsTM))
       -> (rec : (m : Nat) -> Vect m a -> LTE n' m -> (k : Nat ** Vect k a))
       -> (k : Nat ** Vect k a)
drop4PE a n' xsTM xs' pSN'SSxsTM rec = 
    let lteE = lteElim (\l,r, pSN'SSxsTM => (k : Nat ** Vect k a))
                       (\r => ?hole1) -- what do we put here?
                       (\l,r,p, lTErec => rec xsTM xs' (fromLteSucc pSN'SSxsTM))
    in lteE (S n') (S xsTM) pSN'SSxsTM


drop4'V : (a : Type) -> (n' : Nat) -> (m' : Nat) -> Vect (S m') a -> (pSN'SZ : LTE (S n') (S m'))
        -> (rec : (m : Nat) -> Vect m a -> LTE n' m -> (k : Nat ** Vect k a))
        -> (k : Nat ** Vect k a)
drop4'V a n' m' xs pSN'SZ rec = 
    let vE = vecElim a (\m', xs => (pSN'SZ : LTE (S n') m') -> (k : Nat ** Vect k a))
                       (\pSM'1 => (Z ** []))
                       (\xsTM, a', xs', vRec, pSN'SSxsTM => lteElim (\l,r, pSN'SSxsTM => (k : Nat ** Vect k a))
                                                                    (\r => ?hole11) -- what do we put here?
                                                                    (\l,r,p, lTErec => rec xsTM xs' (fromLteSucc pSN'SSxsTM)) (S n') (S xsTM) pSN'SSxsTM)
    in vE (S m') xs pSN'SZ


drop4M'E : (a : Type) -> (n' : Nat) -> (m : Nat) -> Vect m a -> (pSN' : LTE (S n') m)
     -> (rec : (m : Nat) -> Vect m a -> LTE n' m -> (k : Nat ** Vect k a))
     -> (k : Nat ** Vect k a)
drop4M'E a n' m xs pSN' rec =
    let natEM = natElim (\m => Vect m a -> (pSN' : LTE (S n') m) -> (k : Nat ** Vect k a))
                        (\xsEmpty, pSN'Z => (Z ** []))
                        (\m', m'Rec, xs, pSN'SZ => vecElim a (\m', xs => (pSN'SZ : LTE (S n') m') -> (k : Nat ** Vect k a))
                                                             (\pSM'1 => (Z ** []))
                                                             (\xsTM, a', xs', vRec, pSN'SSxsTM => lteElim (\l,r, pSN'SSxsTM => (k : Nat ** Vect k a))
                                                                                                          (\r => ?hole111) -- what do we put here?
                                                                                                          (\l,r,p, lTErec => rec xsTM xs' (fromLteSucc pSN'SSxsTM)) (S n') (S xsTM) pSN'SSxsTM) (S m') xs pSN'SZ)
    in natEM m xs pSN'

drop4 : (a : Type) -> (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m)
     -> (k : Nat ** Vect k a)
drop4 a n m xs p = 
    let natEN = natElim (\n => (m : Nat) -> Vect m a -> (p : LTE n m) -> (k : Nat ** Vect k a))  
                       (\m, xs, pLZ => (m ** xs) ) 
                       (\n', rec, m, xs, pSN' => natElim (\m => Vect m a -> (pSN' : LTE (S n') m) -> (k : Nat ** Vect k a))
                                                         (\xsEmpty, pSN'Z => (Z ** []))
                                                         (\m', m'Rec, xs, pSN'SZ => vecElim a (\m', xs => (pSN'SZ : LTE (S n') m') -> (k : Nat ** Vect k a))
                                                                                            (\pSM'1 => (Z ** []))
                                                                                            (\xsTM, a', xs', vRec, pSN'SSxsTM => lteElim (\l,r, pSN'SSxsTM => (k : Nat ** Vect k a))
                                                                                                                                         (\r => (xsTM ** xs')) -- what do we put here?, technically impossible
                                                                                                                                         (\l,r,p, lTErec => rec xsTM xs' (fromLteSucc pSN'SSxsTM)) (S n') (S xsTM) pSN'SSxsTM) (S m') xs pSN'SZ) m xs pSN')
    in natEN n m xs p

---------------------------------------------------------------------------------------------

drop5 : (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m)
    -> (k : Nat) -> (q : k = m `minus` n)
    -> Vect k a
-- lift the witnesses to the lhs
drop5 Z m xs p k q =
 rewrite q in -- this is systematic, because we're given it
   rewrite minusZeroRight m in -- but where does this come from?
                               -- search the standard library?
                               -- what if we fail?
     xs
drop5 (S n') Z [] p Z q = [] -- still technically impossible
                            -- separate 'prune impossibilities' refac?
drop5 (S n') (S m') (x :: xs) (LTESucc p') k q = 
  case q of
   Refl => ?jj -- drop5 n' m' xs p' k Refl
   -- Refl is a special case?
   -- What if this were a more interesting relation?

{-
eqApply : (x : Type) -> (a : x) -> (b : x) -> (p : a = b) -> a -> b
eqApply x = eqElim x (\a,b,_ => a -> b) (\_, x => x)

drop4M'E : (a : Type) -> (n' : Nat) -> (m : Nat) -> Vect m a -> (pSN' : LTE (S n') m)
     -> (rec : (m : Nat) -> Vect m a -> LTE n' m -> (k : Nat ** Vect k a))
     -> (k : Nat ** Vect k a)
drop4M'E a n' m xs pSN' rec =
    let natEM = natElim (\m => Vect m a -> (pSN' : LTE (S n') m) -> (k : Nat ** Vect k a))
                        (\xsEmpty, pSN'Z => (Z ** []))
                        (\m', m'Rec, xs, pSN'SZ => vecElim a (\m', xs => (pSN'SZ : LTE (S n') m') -> (k : Nat ** Vect k a))
                                                             (\pSM'1 => (Z ** []))
                                                             (\xsTM, a', xs', vRec, pSN'SSxsTM => lteElim (\l,r, pSN'SSxsTM => (k : Nat ** Vect k a))
                                                                                                          (\r => ?hole111) -- what do we put here?
                                                                                                          (\l,r,p, lTErec => rec xsTM xs' (fromLteSucc pSN'SSxsTM)) (S n') (S xsTM) pSN'SSxsTM) (S m') xs pSN'SZ)
    in natEM m xs pSN'


-}

drop6PE : (a : Type) -> (n' : Nat) -> (xsTM : Nat) -> Vect xsTM a -> (pSN'SSxsTM : LTE (S n') (S xsTM))
       -> (k : Nat)
       -> (rec : (m : Nat) -> Vect m a -> LTE n' m -> (k : Nat) -> k = minus m n' -> Vect k a)
       -> (q' : k = minus xsTM n')
       -> Vect k a
drop6PE a n' xsTM xs' pSN'SSxsTM k rec q' = 
    let voidE = voidElim (\_ => Vect k a) ?oo
        lteE = lteElim (\l,r, pSN'SSxsTM => (k : Nat) -> (q : k = minus xsTM n') -> Vect k a)
                       (\r,k,p => rec xsTM xs' (fromLteSucc pSN'SSxsTM) k p) -- what do we put here? Not sure if this is right.
                       (\l,r,p, lTErec,k,p2 => rec xsTM xs' (fromLteSucc pSN'SSxsTM) k p2) -- m' = S (xsTM)
    in lteE (S n') (S xsTM) pSN'SSxsTM k q'


drop6'V : (a : Type) -> (n' : Nat) -> (m' : Nat) -> Vect (S m') a -> (pSN'SZ : LTE (S n') (S m'))
        -> (k : Nat)
        -> (rec : (m : Nat) -> Vect m a -> LTE n' m -> (k : Nat) -> k = minus m n' -> Vect k a)
        -> (p : k = minus m' n')
        -> Vect k a
drop6'V a n' m' xs pSN'SZ k rec p = 
    let k0Vec = eqElim Nat (\k,z,p => Vect z a -> Vect k a)
                                       (\k,v => v)
        vE = vecElim a (\sm', xs => (pSN'SZ : LTE (S n') sm') -> (k : Nat) -> (q : k = minus sm' (S n')) -> Vect k a)
                       (\pSM'1,k,q' => k0Vec k Z q' []) -- []) -- impossible case?
                       (\xsTM, a', xs', vRec, pSN'SSxsTM, k, q' => drop6PE a n' xsTM xs' pSN'SSxsTM k rec q')
    in vE (S m') xs pSN'SZ k p

drop6MEl :  (a : Type) -> (n' : Nat) -> (m : Nat) -> Vect m a -> (p : LTE (S n') m) 
         -> (k : Nat) -> (q : k = m `minus` (S n')) ->  (rec : (m : Nat) -> Vect m a -> LTE n' m -> (k : Nat) -> k = minus m n' -> Vect k a)
         -> Vect k a
drop6MEl a n' m xs p k q rec = 
        let k0Vec = eqElim Nat (\k,z,p => Vect z a -> Vect k a)
                               (\k,v => v)
            elimM = natElim (\m => Vect m a -> (p : LTE (S n') m) -> (k : Nat) -> (q : k = m `minus` (S n')) -> Vect k a)
                            (\xsEmpty, pSN'Z, k, kEqZ => k0Vec k Z kEqZ [])
                            (\m', m'Rec, xs, pSN'SZ, k, pkEqZMN' => drop6'V a n' m' xs pSN'SZ k rec pkEqZMN')
        in elimM m xs p k q

drop6EqE1 : (a : Type) -> (m : Nat) -> Vect m a -> (p : LTE Z m)
         -> (k : Nat) -> (q : k = m `minus` Z)
         -> Vect k a
drop6EqE1 a m xs p k q = 
    let p' = sym q
        eqEl = eqElim Nat 
                      (\mz, m, p => Vect m a -> Vect mz a)
                      (\z, v => v)
                      (m `minus` Z) m (minusZeroRight m) xs
        eq1 = eqElim Nat 
                     (\mz, k, p => Vect mz a -> Vect k a)
                     (\k, v => v)
                     (m `minus` Z) k p' eqEl
    in eq1

drop6 : (a : Type) -> (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m)
    -> (k : Nat) -> (q : k = m `minus` n)
    -> Vect k a
drop6 a n m xs p k q = 
    let natEn = natElim (\n => (m : Nat) -> Vect m a -> (p : LTE n m) -> (k : Nat) -> (q : k = m `minus` n) -> Vect k a) 
                        (\m, xs, pnZm, k, pnZ => drop6EqE1 a m xs pnZm k pnZ)
                        (\n', rec, m, xs, pSZM, k, pkEqSz => drop6MEl a n' m xs pSZM k pkEqSz rec )
    in natEn n m xs p k q