module Drop

import Data.Vect

%default total

drop0 : (n : Nat) -> List a -> List a
drop0 Z xs = xs
drop0 (S n') [] = []
drop0 (S n') (x :: xs) = drop0 n' xs

-------------------------------------------------------------------------------
-- Convert input list to vector, introducing m

-- ddrop' Z xs = (length xs ** xs)
-- ddrop'' Z xs = rewrite lengthCorrect xs in (length xs ** xs)

drop1 : (n : Nat) -> (m : Nat) -> Vect m a -> List a
drop1 Z m xs = toList xs
drop1 (S n') Z [] = []
drop1 (S n') (S m') (x :: xs) = drop1 n' m' xs


-------------------------------------------------------------------------------
-- Convert output list to vector, introducing ∑-type

drop2 : (n : Nat) -> (m : Nat) -> Vect m a -> (k : Nat ** Vect k a) 
drop2 Z m xs = (m ** xs) -- how we get from `toList xs` to this is a mystery.
                         -- Perhaps it is a matter of ordering the refactorings.
                         -- It could also be a matter of library knowledge.
                         -- (i.e. if we know that toList is a function that
                         -- changes List -> Vect, then we know enough to remove
                         -- it.)
drop2 (S n') Z [] = (Z ** [])
drop2 (S n') (S m') (x :: xs) = drop2 n' m' xs

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

-------------------------------------------------------------------------------
-- Lift ∑ to ∏
-- The programmer must give us the relation/restriction.
-- Could this be proven/derived?

drop4 : (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m)
     -> (k : Nat) -> (q : k = m `minus` n)
     -> Vect k a
-- lift the witnesses to the lhs
drop4 Z m xs p k q =
  rewrite q in -- this is systematic, because we're given it
    rewrite minusZeroRight m in -- but where does this come from?
                                -- search the standard library?
                                -- what if we fail?
      xs
drop4 (S n') Z [] p Z q = [] -- still technically impossible
                             -- separate 'prune impossibilities' refac?
drop4 (S n') (S m') (x :: xs) (LTESucc p') k q = 
   case q of
    Refl =>
     drop4 n' m' xs p' k Refl
    -- Refl is a special case?
    -- What if this were a more interesting relation?

test : (n : Nat) -> (m : Nat) -> (p : n = m) -> Bool 
test n n Refl = True 

