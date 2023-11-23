import Data.So
import Decidable.Equality

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

data All : (p : Nat -> Type) -> List Nat -> Type where
    ANil : All p []
    ACons : p x -> All p xs -> All p (x :: xs)
  
filter1 : (a -> Bool) -> List a -> List a
filter1 p [] = []
filter1 p (x :: xs) = if p x then x :: filter1 p xs else filter1 p xs
  
filter11 : (a -> Bool) -> List a -> List a
filter11 p [] = []
filter11 p (x :: xs) = case p x of
    True => x :: filter11 p xs
    False => filter11 p xs
  
-- potentially dead end here?    
filter12 : (Nat -> Bool) -> List Nat -> List Nat
filter12 p [] = []
filter12 p (x :: xs) = case decPred p x of
      (Yes r ** prf) => x :: filter12 p xs
      (No nr ** prf) => filter12 p xs 
      

-- 1.
-- we want to lift filter11 to a type...
-- more precisely, the true case...
-- user selects case
-- only branch that is returning a non-recursive computation is the true case...
-- this introduces Q

-- 2. 
-- other approach (which may be more sensible)
-- user re-specifies return type to be All p applied to output list.
-- this introduces (we can assume All is given):

data Q : (p : Nat -> Bool) -> (x : Nat) -> Type where
  QC : (p : Nat -> Bool) -> (x : Nat) -> (p x = True) -> Q p x

filter13 : (Nat -> Bool) -> List Nat -> (ys : List Nat ** All (\y => Q p y) ys)
filter13 p [] = ([] ** ANil)
filter13 p (x :: xs) = case p x of
      True => ?h1 -- this is the only case that is true, so needs to be refactored.  x :: filter11 p xs
      False => filter13 p xs
   
filter14 : (Nat -> Bool) -> List Nat -> (ys : List Nat ** All (\y => Q p y) ys)
filter14 p [] = ([] ** ANil)
filter14 p (x :: xs) = case p x of
   -- True => (x :: ?weneedthis... ** ? and we need this... ) -- this is the only case that is true, so needs to be refactored.  x :: filter11 p xs
    True => case filter14 p xs of -- where do we get this recursive call from? "a generative fold?"
                (ys ** p) => (ys ** ?filter14_1) 
    False => filter14 p xs
  
{-
filter15 : (Nat -> Bool) -> List Nat -> (ys : List Nat ** All (\y => Q p y) ys)
filter15 p [] = ([] ** ANil)
filter15 p (x :: xs) = case p x of
    -- True => (x :: ?weneedthis... ** ? and we need this... ) -- this is the only case that is true, so needs to be refactored.  x :: filter11 p xs
    True => case filter15 p xs of -- where do we get this recursive call from? "a generative fold?"
                  (ys ** p) => (ys ** ACons ?filter15_1 ?filter15_2) -- fill in the hole... 
                                                                     -- but we can't as ACons requires more information...
    False => filter15 p xs
-}

-- by original equation
-- filter15 (x::xs) = case p x of True => x :: filter15 xs... 
filter15 : (Nat -> Bool) -> List Nat -> (ys : List Nat ** All (\y => Q p y) ys)
filter15 p [] = ([] ** ANil)
filter15 p (x :: xs) = case p x of
   -- True => (x :: ?weneedthis... ** ? and we need this... ) -- this is the only case that is true, so needs to be refactored.  x :: filter11 p xs
    True => case filter15 p xs of -- where do we get this recursive call from? "a generative fold?"
                (ys ** p) => (x::ys ** ACons ?filter15_1 ?filter15_2) 
    False => filter15 p xs

-- inspecting the holes... 
-- we try to add p as second parameter to ACons
filter16 : (p: Nat -> Bool) -> List Nat -> (ys : List Nat ** All (\y => Q p y) ys)
filter16 p [] = ([] ** ANil)
filter16 p (x :: xs) = case p x of
   -- True => (x :: ?weneedthis... ** ? and we need this... ) -- this is the only case that is true, so needs to be refactored.  x :: filter11 p xs
    True => case filter15 p xs of -- where do we get this recursive call from? "a generative fold?"
                (ys ** p2) => (x::ys ** ACons ?filter16_1 p2) 
    False => filter16 p xs

-- inspecting the holes... 
-- first param to ACons requires a proof of Q ... 
-- we introduce a proof and leave holes
-- this is done by standard technique of introducing a new definition

q_prf : (p : Nat -> Bool) -> (x : Nat) -> Q p x
q_prf p x = QC p x ?q_prf3

filter17 : (p : Nat -> Bool) -> List Nat -> (ys : List Nat ** All (\y => Q p y) ys)
filter17 p [] = ([] ** ANil)
filter17 p (x :: xs) = case p x of
   -- True => (x :: ?weneedthis... ** ? and we need this... ) -- this is the only case that is true, so needs to be refactored.  x :: filter11 p xs
    True => case filter17 p xs of -- where do we get this recursive call from? "a generative fold?"
                (ys ** p2) => (x::ys ** ACons (q_prf p x) p2) 
    False => filter17 p xs

-- we have arrived at needing a proof that
-- p x = True
filter18 : (p : Nat -> Bool) -> List Nat -> (ys : List Nat ** All (\y => Q p y) ys)
filter18 p [] = ([] ** ANil)
filter18 p (x :: xs) = case p x of
       -- True => (x :: ?weneedthis... ** ? and we need this... ) -- this is the only case that is true, so needs to be refactored.  x :: filter11 p xs
        True => case filter18 p xs of -- where do we get this recursive call from? "a generative fold?"
                    (ys ** p2) => (x::ys ** ACons (q_prf p x) p2) 
        False => filter18 p xs
