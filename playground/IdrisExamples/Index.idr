module Index

import Data.Nat
import Data.Vect

%default total

index0 : (i : Nat) -> List a -> Maybe a
index0 i [] = Nothing
index0 Z (x :: xs) = Just x
index0 (S i') (x :: xs) = index0 i' xs

-------------------------------------------------------------------------------
-- Convert first list

index1 : (i : Nat) -> (n : Nat) -> Vect n a -> Maybe a
index1 i Z [] = Nothing
index1 Z (S n') (x :: xs) = Just x
index1 (S i') (S n') (x :: xs) = index1 i' n' xs

-------------------------------------------------------------------------------
-- Narrow domain

index2 : (i : Nat) -> (n : Nat) -> Vect n a -> (p : LT i n) -> Maybe a
index2 i Z [] p = Nothing
index2 Z (S n') (x :: xs) p = Just x
index2 (S i') (S n') (x :: xs) (LTESucc p') = index2 i' n' xs p'

-------------------------------------------------------------------------------
-- Unfold LT

index3 : (i,n : Nat) -> Vect n a -> (p : LTE (S i) n) -> Maybe a
index3 i Z [] p = Nothing
index3 Z (S n') (x :: xs) p = Just x
index3 (S i') (S n') (x :: xs) (LTESucc p') = index3 i' n' xs p'

-------------------------------------------------------------------------------
-- Prune impossibilities
-- pattern match on the proof term to figure out if we can reach absurdity
-- how feasible?

index4 : (i,n : Nat) -> Vect n a -> (p : LTE (S i) n) -> Maybe a
index4 Z Z [] LTEZero impossible
index4 (S i') Z [] (LTESucc p') impossible
index4 Z (S n') (x :: xs) (LTESucc p') = Just x
index4 (S i') (S n') (x :: xs) (LTESucc p') = index4 i' n' xs p'

-- this has removed all nothings, which means...

-------------------------------------------------------------------------------
-- Remove Maybe
-- in cases where no Nothings are returned, we can safely strip away the maybe

index5 : (i,n : Nat) -> Vect n a -> (p : LTE (S i) n) -> a
index5 Z (S n') (x :: xs) (LTESucc p') = x
index5 (S i') (S n') (x :: xs) (LTESucc p') = index5 i' n' xs p'


-- does insertAt, deleteAt, replaceAt, and updateAt follow similarly?
-- https://github.com/idris-lang/Idris2/blob/main/libs/base/Data/Vect.idr 

{-
-------------------------------------------------------------------------------
-- Prune impossibilities
-- pattern match on the proof term to figure out if we can reach absurdity
-- how feasible?

index3 : (i : Nat) -> (n : Nat) -> Vect n a -> (p : LTE i n) -> Maybe a
index3 Z Z [] LTEZero = Nothing
  -- this isn't impossible and so we can't remove all the nothings...
  -- special refactoring for removing maybe?
  -- it is something of a pattern... -> Maybe a => -> a
index3 (S i') Z [] LTEZero impossible
index3 Z Z [] (LTESucc p') impossible
index3 (S i') Z [] (LTESucc p') impossible
index3 Z (S n') (x :: xs) LTEZero = Just x
index3 (S i') (S n') (x :: xs) (LTESucc p') = index3 i' n' xs p'

-------------------------------------------------------------------------------
-- Add NonZero (another constraint)

index4 : (i : Nat) -> (n : Nat) -> Vect n a -> (p : LTE i n) -> (q : NonZero n)
      -> Maybe a
index4 Z Z [] LTEZero SIsNonZero impossible -- now we get rid of it
index4 Z (S n') (x :: xs) LTEZero SIsNonZero = Just x
index4 (S i') (S n') (x :: xs) (LTESucc p') SIsNonZero =
  case n' of
    Z => ?h1
    S n'' => ?h2
  -- index4 i' n' xs p' ?h1
 -}
