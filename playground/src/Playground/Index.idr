module Index

import Data.Nat
import Data.Fin 
import Data.Vect
import Data.List

import RefacPrelude

{-
index0 : (i : Nat) -> List a -> Maybe a
index0 i [] = Nothing
index0 Z (x :: xs) = Just x
index0 (S i') (x :: xs) = index0 i' xs
-}

index0 : (a : Type) -> (i : Nat) -> List a -> Maybe a
index0 a i xs = listElim a (\l => (i : Nat) -> Maybe a) 
                           (\i => Nothing)
                           (\x, xs, rec,i => natElim (\i => Maybe a) (Just x) (\i',recN => rec i') i) xs i


{-
-------------------------------------------------------------------------------
-- Convert first list

index1 : (i : Nat) -> (n : Nat) -> Vect n a -> Maybe a
index1 i Z [] = Nothing
index1 Z (S n') (x :: xs) = Just x
index1 (S i') (S n') (x :: xs) = index1 i' n' xs
-}

index1 : (a : Type) -> (i : Nat) -> (n : Nat) -> Vect n a -> Maybe a
index1 a i n xs = vecElim a (\n,l => (i : Nat) -> Maybe a) 
                            (\i => Nothing)
                            (\n',x, xs, rec,i => natElim (\i => Maybe a) (Just x) (\i',recN => rec i') i) n xs i


{-
-------------------------------------------------------------------------------
-- Narrow domain

index2 : (i : Nat) -> (n : Nat) -> Vect n a -> (p : LT i n) -> Maybe a
index2 i Z [] p = Nothing
index2 Z (S n') (x :: xs) p = Just x
index2 (S i') (S n') (x :: xs) (LTESucc p') = index2 i' n' xs p'
-}

index2LE : (a : Type) -> (i' : Nat) -> (n' : Nat) -> (p : LTE (S (S i')) (S n')) 
        -> (rec : (i : Nat) -> LTE (S i) n' -> Maybe a) -> Maybe a
index2LE a i' n' p rec = 
    let lE = lteElim (\l,r,p => Maybe a) (\ssi => rec i' (fromLteSucc p)) (\l,r,p2,recL => rec i' (fromLteSucc p))
    in lE (S (S i')) (S n') p

index2NE : (a : Type) -> (i : Nat) -> (n' : Nat) -> (x : a) -> (xs : Vect n' a) -> (p : LTE (S i) (S n')) 
        -> (rec : (i : Nat) -> LTE (S i) n' -> Maybe a) -> Maybe a
index2NE a i n' x xs p rec =
    let nE = natElim (\i => (p : LTE (S i) (S n')) -> Maybe a) (\p => Just x) (\i', rec2, p2 => index2LE a i' n' p2 rec)
    in nE i p

index2' : (a : Type) -> (i : Nat) -> (n : Nat) -> Vect n a -> (p : LTE (S i) n) ->  Maybe a
index2' a i n xs p = 
    let vE = vecElim a (\n,l => (i : Nat) -> (p : LTE (S i) n) -> Maybe a) 
                              (\i,p => Nothing)
                              (\n',x, xs, rec,i,p2 => index2NE a i n' x xs p2 rec) -- natElim (\i => (p : LTE (S i) n) -> Maybe a) (\p => Just x) (\i',recN, p => rec i' p) i p2) n xs i p
    in vE n xs i p

-- inlined version

index2 : (a : Type) -> (i : Nat) -> (n : Nat) -> Vect n a -> (p : LTE (S i) n) ->  Maybe a
index2 a i n xs p = 
    let vE = vecElim a (\n,l => (i : Nat) -> (p : LTE (S i) n) -> Maybe a) 
                              (\i,p => Nothing)
                              (\n',x, xs, rec,i,p2 => 
                                 natElim (\i => (p : LTE (S i) (S n')) -> Maybe a) 
                                         (\p => Just x) 
                                         (\i', rec2, p3 => 
                                            lteElim (\l,r,p => Maybe a) 
                                                    (\ssi => rec i' ?j ) --(fromLteSucc p3)) 
                                                    (\l,r,p4,recL => rec i' (fromLteSucc p3)) (S (S i')) (S n') p3 ) i p2) 
    in vE n xs i p

{-
-------------------------------------------------------------------------------
-- Prune impossibilities
-- pattern match on the proof term to figure out if we can reach absurdity
-- how feasible?

index4 : (i,n : Nat) -> Vect n a -> (p : LTE (S i) n) -> Maybe a
index4 Z Z [] LTEZero impossible
index4 (S i') Z [] (LTESucc p') impossible
index4 Z (S n') (x :: xs) (LTESucc p') = Just x
index4 (S i') (S n') (x :: xs) (LTESucc p') = index4 i' n' xs p'
 

index4 []        Z      Z      LTEZero impossible
index4 []        (S i') Z      (LTESucc p') impossible
index4 (x :: xs) Z      (S n') (LTESucc p') = Just x
index4 (x :: xs) (S i') (S n') (LTESucc p') = index4 i' n' xs p'

-}

------
-- empty case 
-- we want to eliminate on the lte
-- the point is that it should be impossible to eliminate when the vector is empty as there is nothing to return.
-- we should return Just Type ... 
------
-------
-- none empty case, eliminate as normal.
------
{-
index2 : (a : Type) -> (i : Nat) -> (n : Nat) -> Vect n a -> (p : LTE (S i) n) ->  Maybe a
index2 a i n xs p = 
    let vE = vecElim a (\n,l => (i : Nat) -> (p : LTE (S i) n) -> Maybe a) 
                              (\i,p => Nothing)
                              (\n',x, xs, rec,i,p2 => 
                                 natElim (\i => (p : LTE (S i) (S n')) -> Maybe a) 
                                         (\p => Just x) 
                                         (\i', rec2, p3 => 
                                            lteElim (\l,r,p => Maybe a) 
                                                    (\ssi => rec i' (fromLteSucc p3)) 
                                                    (\l,r,p4,recL => rec i' (fromLteSucc p3)) (S (S i')) (S n') p3 ) i p2) 
    in vE n xs i p
-}

index4 : (a : Type) -> (i : Nat) -> (n : Nat) -> Vect n a -> (p : LTE (S i) n) ->  Maybe a
index4 a i n xs p = 
    let vE = vecElim a (\n,l => (i : Nat) -> (p : LTE (S i) n) -> Maybe a) 
                              (\i,p => lteElim (\si,z,_ => Maybe a)
                                               (\l => voidElim (\_ => Maybe a) (pSnIsNot0 i (antisym (S i) Z p LTEZero)))
                                               (\l,r,p2,m => voidElim (\_ => Maybe a) (pSnIsNot0 i (antisym (S i) Z p LTEZero))) (S i) Z p )
                              (\n',x, xs, rec,i,p2 => natElim (\i => (p : LTE (S i) (S n')) -> Maybe a) 
                                                              (\p => Just x) 
                                                              (\i', rec2, p2 => 
                                                                  lteElim (\l,r,p => Maybe a) (\ssi => rec i' (fromLteSucc2 (S i') n' p2)) (\l,r,p3,recL => rec i' (fromLteSucc2 (S i') n' p2))
                                                                                     (S (S i')) (S n') p2) i p2 )
    in vE n xs i p

{-
-------------------------------------------------------------------------------
-- Remove Maybe
-- in cases where no Nothings are returned, we can safely strip away the maybe

index5 : (i,n : Nat) -> Vect n a -> (p : LTE (S i) n) -> a
index5 Z (S n') (x :: xs) (LTESucc p') = x
index5 (S i') (S n') (x :: xs) (LTESucc p') = index5 i' n' xs p'

-}

index5 : (a : Type) -> (i : Nat) -> (n : Nat) -> Vect n a -> (p : LTE (S i) n) ->  a
index5 a i n xs p = 
    let vE = vecElim a (\n,l => (i : Nat) -> (p : LTE (S i) n) -> a) 
                              (\i,p => lteElim (\si,z,_ => a)
                                               (\l =>  voidElim (\_ => a) (pSnIsNot0 i (antisym (S i) Z p LTEZero)))
                                               (\l,r,p2,m => voidElim (\_ => a) (pSnIsNot0 i (antisym (S i) Z p LTEZero))) (S i) Z p )
                              (\n',x, xs, rec,i,p2 => natElim (\i => (p : LTE (S i) (S n')) -> a) 
                                                              (\p => x) 
                                                              (\i', rec2, p2 => 
                                                                  lteElim (\l,r,p => a) (\ssi => rec i' (fromLteSucc2 (S i') n' p2)) (\l,r,p3,recL => rec i' (fromLteSucc2 (S i') n' p2))
                                                                                     (S (S i')) (S n') p2) i p2 )
    in vE n xs i p


example4 : Maybe Nat 
example4 = index4 Nat 3 5 [1,2,3,4,5] (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))

example5 : Maybe Nat 
example5 = index4 Nat 3 5 [1,2,3,4,5] (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))