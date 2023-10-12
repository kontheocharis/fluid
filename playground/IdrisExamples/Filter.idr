module Filter

import Data.Vect

%default total

filter0 : (p : a -> Bool) -> List a -> List a
filter0 p [] = []
filter0 p (x :: xs) = if p x then x :: filter0 p xs else filter0 p xs

-------------------------------------------------------------------------------
-- Lift rec call

filter1 : (p : a -> Bool) -> List a -> List a
filter1 p [] = []
filter1 p (x :: xs) =
  let xs' = filter1 p xs
  in if p x then x :: xs' else xs'

-------------------------------------------------------------------------------
-- Convert input list

filter2 : (p : a -> Bool) -> (n : Nat) -> Vect n a -> List a
filter2 p Z [] = []
filter2 p (S n') (x :: xs) =
  let xs' = filter2 p n' xs
  in if p x then x :: xs' else xs'

-------------------------------------------------------------------------------
-- Convert output list, ∑-type

filter3 : (p : a -> Bool) -> (n : Nat) -> Vect n a -> (k : Nat ** Vect k a)
filter3 p Z [] = (Z ** [])
filter3 p (S n') (x :: xs) =
  let (k' ** xs') = filter3 p n' xs -- known b/c the return type changed
  in if p x then (S k' ** x :: xs') else (k' ** xs')
  -- introduce ∑s here to inhabit return type, witnesses are derived from proof
  -- and existing information

-------------------------------------------------------------------------------
-- To make it more interesting...
-- Lift ∑ to ∏

filter4 : (p : a -> Bool) -> (n : Nat) -> Vect n a
       -> (k : Nat) -> (q : LTE k n)
       -> Vect k a
filter4 p Z [] Z q = []
  -- case split on q, which updates k, to get recursive call
filter4 p (S n') (x :: xs) Z LTEZero = [] -- but this changes the meaning...
  -- ^ case now means that we provide an upper bound on the filtered list
  -- this is necessarily bad...?
  -- do we want to add another relation as part of this step?
  -- but that's only if we consider actual meaning, what if we treat these as 
  -- the arbitrary functions they are?
filter4 p (S n') (x :: xs) (S k') (LTESucc q') =
  let xs' = filter4 p n' xs k' q'
  -- in x :: xs'
  -- this ultimately breaks because we've gotten rid of the choice
  -- Filter> filter4 (>3) 4 [2,3,4,5] 2 (LTESucc (LTESucc LTEZero))
  -- [2, 3]
  -- Filter> filter4 (>3) 4 [2,3,4,5] Z LTEZero
  -- []
  -- Filter> filter4 (>3) 4 [2,3,4,5] 3 (LTESucc (LTESucc (LTESucc LTEZero)))
  -- [2, 3, 4]
  in if p x then x :: xs' else ?filter4Error :: xs'
  -- alternatively, do we simply fill this with x, obtained from the
  -- assumptions?

-- this raises the question as to what happens when the relation given isn't
-- 'strong enough' to capture the original behaviour.

-- Questions are also raised about call sites...

-------------------------------------------------------------------------------
-- To make it more interesting...
-- Lift ∑ to ∏
-- A stronger relation

-- assume we are given this (library definition?)
data VectAll : (p : a -> Bool) -> (xs : Vect n a) -> Type where
  ANil : VectAll p []
  ACons : {p : a -> Bool} -> {x : a} -> So (p x) -> VectAll p (x :: xs)

data FVLen : (p : a -> Bool) -> (k : Nat) -> (xs : Vect n a) -> Type where
  FVLNil : FVLen p Z []
  FVLConsTT : {p : a -> Bool} -> {x : a}
           -> So (p x)
           -> FVLen p k xs
           -> FVLen p (S k) (x :: xs)
  FVLConsFF : {p : a -> Bool} -> {x : a}
          -> So (not (p x))
          -> FVLen p k xs
          -> FVLen p k (x :: xs)

data Pred : (p : a -> Bool) -> (n,k : Nat) -> (xs : Vect n a) -> Type where
  MkPred : LTE k n -> FVLen p k xs -> Pred p n k xs

-- although, by this point, we're already calculating filter in the type...
-- this is too unrealistic...
-- the sort of predicates we're introducing should be simple arithmetical ones

filter4' : (p : a -> Bool) -> (n : Nat) -> (xs : Vect n a)
        -> (k : Nat) -> (q : Pred p n k xs)
        -> Vect k a
filter4' p Z [] Z q = []
filter4' p Z [] (S k') (MkPred q1 q2) = absurd q1 -- missing clause, otherwise
filter4' p (S n') (x :: xs) Z (MkPred LTEZero q2) = [] -- magic?
filter4' p (S n') (x :: xs) (S k') (MkPred (LTESucc q1') q2) =
  case q2 of -- magically replaces the if...???
    FVLConsTT q21 q22 =>
      let xs' = filter4' p n' xs k' (MkPred q1' q22)
      in x :: xs'
    FVLConsFF q21 q22 =>
      filter4' p n' xs (S k') (MkPred ?f4' q22) -- you need a lemma for this
        -- LTK k' n' -> LTE (S k') n', which is not true in the general case
      -- This is a rabbit hole. Abandoning.
