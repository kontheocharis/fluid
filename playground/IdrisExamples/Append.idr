module Append

import Data.Nat
import Data.Vect

%default total

app0 : List a -> List a -> List a
app0 [] ys = ys
app0 (x :: xs) ys = x :: (app0 xs ys)

-------------------------------------------------------------------------------
-- Convert first list

app1 : (n : Nat) -> Vect n a -> List a -> List a
app1 Z [] ys = ys
app1 (S n') (x :: xs) ys = x :: (app1 n' xs ys)

-------------------------------------------------------------------------------
-- Convert second list

app2 : (n : Nat) -> Vect n a -> (m : Nat) -> Vect m a -> List a
app2 Z [] m ys = toList ys -- again, assume known converter
app2 (S n') (x :: xs) m ys = x :: (app2 n' xs m ys)

-------------------------------------------------------------------------------
-- Convert third list

app3 : (n : Nat) -> Vect n a -> (m : Nat) -> Vect m a
    -> (k : Nat ** Vect k a)
app3 Z [] m ys = (m ** ys) -- again, that sort of magic from before
                           -- is there a general rule here?
app3 (S n') (x :: xs) m ys =
  let (k ** zs) = app3 n' xs m ys -- lift recursive call into irrefutable p.m.
  in (S k ** x :: zs)

-------------------------------------------------------------------------------
-- Lift ∑ to ∏

app4 : (n : Nat) -> Vect n a -> (m : Nat) -> Vect m a
    -> (k : Nat) -> (p : k = n + m)
    -> Vect k a
app4 Z [] m ys m Refl = ys
  -- case split on k...
app4 (S n') (x :: xs) m ys (plus (S n') m) Refl =
  let zs = app4 n' xs m ys (plus n' m) Refl
  in x :: zs

-- app4 (S n') (x :: xs) m ys Z p = [] -- absurd p
-- app4 (S n') (x :: xs) m ys (S k') p =
--   let zs = app4 n' xs m ys k' (injective p) -- whence injective p? prf search?
--   in x :: zs
