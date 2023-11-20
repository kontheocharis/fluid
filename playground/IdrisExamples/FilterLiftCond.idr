import Data.So
import Decidable.Equality

-- filter0 : (a -> Bool) -> [a] -> [a]
-- filter0 p [] = []
-- filter0 p (x :: xs) | p x = x :: filter0 p xs
--                     | otherwise = filter0 p xs

-- data Map : (f : a -> b -> Type) -> List a -> List b -> Type where
--   LNil : Map f [] []
--   LCons : (f x y) -> Map f xs ys -> Map f (x :: xs) (y :: ys)

-- data MySo : Bool -> Type where
--   C : (t : Bool) -> So t -> MySo t

-- P : (a -> Bool) -> a -> Type
-- P p x = MySo (p x)

-- data All : (p : a -> Type) -> List a -> Type where
--   ANil : All p []
--   ACons : p x -> All p xs -> All p (x :: xs)

-- Q : (a -> Bool) -> List a -> Type
-- Q p xs = All (\x => So (p x)) xs



-- filter2 : (p : Nat -> Bool) -> (xs : List Nat) -> (ys : List Nat ** Q p ys)
-- filter2 p [] = ([] ** ANil)
-- filter2 p (x :: xs) = case p x of
--   True => ?h1
--   --  case filter2 p xs of
--   --   (ys ** q) => ((x :: ys) ** (?h1))
--   False => case filter2 p xs of
--     (ys ** q) => (ys ** q)

------------------------------------------------------------------------------

data DecPred : (p : Nat -> Bool) -> (x : Nat) -> Dec (p x = True) -> Type where
  DPYes : (p : Nat -> Bool) -> (x : Nat) -> (q : ((p x) = True))
       -> DecPred p x (Yes q)
  DPNo  : (p : Nat -> Bool) -> (x : Nat) -> (q : Not ((p x) = True))
       -> DecPred p x (No q)

decPred : (p : Nat -> Bool) -> (x : Nat)
       -> (q : Dec (p x = True) ** DecPred p x q)
decPred p x = case decEq (p x) True of
  Yes q => let prf = DPYes p x q in (Yes q ** prf)
  No nq => let prf = DPNo p x nq in (No nq ** prf)

filter1 : (a -> Bool) -> List a -> List a
filter1 p [] = []
filter1 p (x :: xs) = if p x then x :: filter1 p xs else filter1 p xs

filter11 : (a -> Bool) -> List a -> List a
filter11 p [] = []
filter11 p (x :: xs) = case p x of
  True => x :: filter11 p xs
  False => filter11 p xs

filter12 : (a -> Bool) -> List a -> List a
filter12 p [] = []
filter12 p (x :: xs) = case p x of
  True => case filter12 p xs of
    ys => x :: ys
  False => case filter12 p xs of
    ys => ys

data All : (p : Nat -> Type) -> List Nat -> Type where
  ANil : All p []
  ACons : p x -> All p xs -> All p (x :: xs)

data Q : (p : Nat -> Bool) -> (x : Nat) -> Type where
  QC : (p : Nat -> Bool) -> (x : Nat) -> (p x = True) -> Q p x

filter2 : (p : Nat -> Bool) -> (xs : List Nat)
       -> (ys : List Nat ** All (\y => Q p y) ys)
filter2 p [] = ([] ** ANil)
filter2 p (x :: xs) = case decPred p x of
  (Yes r ** prf) => case filter2 p xs of
    (ys ** prf1) =>
      let q = QC p x r
      in ((x :: ys) ** ACons q prf1)
  (No nr ** prf) => case filter2 p xs of
    (ys ** prf1) => (ys ** prf1)
