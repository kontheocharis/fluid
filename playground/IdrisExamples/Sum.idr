
sum : List Nat -> Nat 
sum [] = Z 
sum (h::t) = (+) h (sum t)

main = sum [1,2,3,4]

--- first step, lift to a type...

data Sum : List Nat -> Nat -> Type where 
   C1 : Sum [] Z 
   C2 : (h : Nat) -> (t : List Nat) -> (t' : Nat) -> (rec : Sum t t') -> Sum (h::t) ((+) h t')

sum2 : (xs : List Nat) -> (xs' ** Sum xs xs')
sum2 [] = (Z ** C1)
sum2 (h::t) = case sum2 t of 
                (t' ** sp) => (((+) h t') ** C2 h t t' sp)

-- Step1 Generalise Sum .. 
-- Generalise Z in first constructor...
-- Generalise (+) in second constructor ...
data Sum2 : List Nat -> Nat -> Type where 
   C12 : (n : Nat) -> Sum2 [] n 
   C22 : (f : Nat -> Nat -> Nat) -> (h : Nat) -> (t : List Nat) -> (t' : Nat) -> (rec : Sum2 t t') -> Sum2 (h::t) (f h t')

sum3 : (xs : List Nat) -> (xs' ** Sum2 xs xs')
sum3 [] = (Z ** C12 Z)
sum3 (h::t) = case sum3 t of 
                (t' ** sp) => (((+) h t') ** C22 (+) h t t' sp)


-- Step2 Sum is renamed to Fold .. 
data Fold : List Nat -> Nat -> Type where 
   C12' : (n : Nat) -> Fold [] n 
   C22' : (f : Nat -> Nat -> Nat) -> (h : Nat) -> (t : List Nat) -> (t' : Nat) -> (rec : Fold t t') -> Fold (h::t) (f h t')

sum4 : (xs : List Nat) -> (xs' ** Fold xs xs')
sum4 [] = (Z ** C12' Z)
sum4 (h::t) = case sum4 t of 
                (t' ** sp) => (((+) h t') ** C22' (+) h t t' sp)

main2 = sum4 [1,2,3,4]

-- main2 :: Fold (+) 0 [1,2,3,4] 

-- Step3 Fold is generalised at the index level over the function and base case ... 
-- Step3 a -- function 
data Fold2 : (Nat -> Nat -> Nat) -> List Nat -> Nat -> Type where 
   C12'' : (f : Nat -> Nat -> Nat) -> (n : Nat) -> Fold2 f [] n 
   C22'' : (f : Nat -> Nat -> Nat) -> (h : Nat) -> (t : List Nat) -> (t' : Nat) -> (rec : Fold2 f t t') -> Fold2 f (h::t) (f h t')

sum5 : (xs : List Nat) -> (xs' ** Fold2 (+) xs xs')
sum5 [] = (Z ** C12'' (+) Z)
sum5 (h::t) = case sum5 t of 
                (t' ** sp) => (((+) h t') ** C22'' (+) h t t' sp)

-- remove need for xs' 
sum6 : (xs : List Nat) -> (b : Nat) -> Fold2 (+) xs b
sum6 [] Z = C12'' (+) Z
sum6 [] (S n) = C12'' (+) (S n) 
sum6 (h::t) b = case sum6 t b of 
                sp => C22'' ?h5 ?h4 ?H3 ?h2 ?h1 -- C22'' (+) h t t' sp)
