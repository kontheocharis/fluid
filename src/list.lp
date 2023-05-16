-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ

let listAppend = 
   (\a xs ys -> 
        listElim a 
                 (\l -> List a -> List a) 
                 (\ys -> ys) 
                 (\x xs rec ys -> LCons a x (rec ys)) xs ys
   ) :: forall (a :: *) (xs :: List a) (ys :: List a). List a

let listAppend3 = 
    (\a n xs ys ->
        vecElim a 
                (\n l -> List a -> List a)
                (\ys -> ys)
                (\m x xs rec ys ->  LCons a x (rec ys))
                n xs ys
    ) :: forall (a :: *) (n :: Nat) (xs :: Vec a n) (ys :: List a) . List a


let listAppend5 = 
    (\a n xs m ys ->
        vecElim a
                (\n l -> forall (m :: Nat) . Vec a m -> List a)
                (\m ys -> vecToList a m ys)
                (\m x xs rec m ys -> LCons a x (rec m ys))
                n xs m ys
    ) :: forall (a :: *) (n :: Nat) (xs :: Vec a n) (m :: Nat) (ys :: Vec a m) . List a

let pairT1 = Pair Nat (Succ Zero) (\n -> Vec Nat n) (Cons Nat 0 1 (Nil Nat))  
                :: Sigma Nat (\x -> Vec Nat x)

let listAppend6 =
    ( \a n xs m ys ->
        vecElim a 
                (\n l -> forall (m :: Nat) . Vec a m -> Sigma Nat (\o -> Vec a o))
                (\m ys -> Pair Nat m (\n -> Vec a n) ys)                
                (\m x xs rec m ys -> sigElim Nat 
                                             (\o -> Vec a o)
                                             (\a' -> Sigma Nat (\o -> Vec a o))
                                             (\o vo -> Pair Nat (Succ o) (\o -> Vec a o) (Cons a o x vo)) 
                                             (rec m ys)
                ) n xs m ys

    ) :: forall (a :: *) (n :: Nat) (xs :: Vec a n) (m :: Nat) (ys :: Vec a m) . Sigma Nat (\o -> Vec a o)

let listAppend7 = 
    ( \a n xs m ys ->
        vecElim a
                (\n  l -> forall (m :: Nat) . Vec a m -> Vec a (plus n m))
                (\m ys -> ys)
                (\a' x xs rec m ys -> Cons a (plus a' m) x (rec m ys))
                n xs m ys
    ) :: forall (a :: *) (n :: Nat) (xs :: Vec a n) (m :: Nat) (ys :: Vec a m) . Vec a (plus n m)