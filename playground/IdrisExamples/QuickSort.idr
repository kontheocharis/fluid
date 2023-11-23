ifThenElse : (b : Bool) -> (b = True -> a) -> (b = False -> a) -> a
ifThenElse True f g = f Refl
ifThenElse False f g = g Refl

filter1 : (p : Nat -> Bool) -> List Nat -> List Nat
filter1 p [] = []
filter1 p (x::xs) = ifThenElse (p x)
  (\_ => let
      ys = filter1 p xs
    in x::ys)
  (\_ => let
      ys = filter1 p xs
    in ys)

data Filtered : (Nat -> Bool) -> List Nat -> List Nat -> Type where
  FNil : Filtered p [] []
  FConsTrue : (p x = True) -> Filtered p xs ys -> Filtered p (x :: xs) (x :: ys)
  FConsFalse : (p x = False) -> Filtered p xs ys -> Filtered p (x :: xs) ys

-- Recovering All from Filtered
All : (Nat -> Bool) -> List Nat -> Type
All p xs = (ys : List Nat ** Filtered p ys xs)

filter1' : (p : Nat -> Bool) -> (xs : List Nat) -> (ys : List Nat ** Filtered p xs ys)
filter1' p [] = ([] ** FNil)
filter1' p (x::xs) = ifThenElse (p x)
  (\m => let
      (ys ** q) = filter1' p xs
    in ((x::ys) ** FConsTrue m q))
  (\m => let
      (ys ** q) = filter1' p xs
    in (ys ** FConsFalse m q))

-- Recovering refined filter from other example, from filter1'
filter1'' : (p : Nat -> Bool) -> (xs : List Nat) -> (ys : List Nat ** All p ys)
filter1'' p xs = let (ys ** q) = filter1' p xs in (ys ** (xs ** q))

-- Same idea for sorting:

-- This is refined to match the structure of quicksort! Other proofs of sorting
-- are possible but require MUCH more work to *type quicksort with*.
data QSorted : List Nat -> List Nat -> Type where
  QNil : QSorted [] []
  QCons : (Filtered (< x) xs as) -> (Filtered (>= x) xs bs) -> (QSorted as as') -> (QSorted bs bs') -> QSorted (x::xs) (as' ++ [x] ++ bs')

qsort : List Nat -> List Nat
qsort [] = []
qsort (x::xs) = let
    as = filter1 (< x) xs
    bs = filter1 (>= x) xs
    as' = qsort as
    bs' = qsort bs
  in as' ++ [x] ++ bs'

qsort' : (xs : List Nat) -> (ys : List Nat ** QSorted xs ys)
qsort' [] = ([] ** QNil)
qsort' (x::xs) = let
    (as ** asF) = filter1' (< x) xs
    (bs ** bsF) = filter1' (>= x) xs
    (as' ** asS) = qsort' as
    (bs' ** bsS) = qsort' bs
  in ((as' ++ [x] ++ bs') ** QCons asF bsF asS bsS)

IsSorted : (ys : List Nat) -> Type
IsSorted ys = (xs : List Nat ** QSorted xs ys)

qsort'' : (xs : List Nat) -> (ys : List Nat ** IsSorted ys)
qsort'' xs = let (ys ** p) = qsort' xs in (ys ** (xs ** p))
