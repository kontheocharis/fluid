-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ

let length = 
  (\ a xs -> listElim a 
             (\xs -> Nat)
             Zero 
             (\x xs rec -> plus 1 rec ) xs
  ) :: forall (a :: *) (xs :: List a) . Nat 

let vectToList = 
  ( \ a n xs -> vecElim a 
                        (\n xs -> List a)
                        (LNil a)
                        (\n x xs rec -> LCons a x rec) n xs

  ) :: forall (a :: *) (n :: Nat) (xs :: Vec a n) . List a 

let appendL = 
    (\ a xs ys ->
                    listElim a
                             (\xs -> forall (ys :: List a) . List a) 
                             (\ys -> ys)
                             (\x xs rec ys -> LCons a x (rec ys)) 
                             xs ys 
    ) :: forall (a :: *) (xs :: List a) (ys :: List a) . List a 

let appendL3 = 
    (\ a n xs ys ->
                    vecElim a
                             (\n xs -> forall (ys :: List a) . List a) 
                             (\ys -> ys)
                             (\n x xs rec ys -> LCons a x (rec ys)) 
                             n xs ys 
    ) :: forall (a :: *) (n :: Nat) (xs :: Vec a n) (ys :: List a) . List a 

let appendL4 = 
    (\ a n xs m ys ->
                    vecElim a
                             (\n xs -> forall (ys :: List a) . List a) 
                             (\ys -> ys)
                             (\n x xs rec ys -> LCons a x (rec ys)) 
                             n xs (vectToList a m ys) 
    ) :: forall (a :: *) (n :: Nat) (xs :: Vec a n) (m :: Nat) (ys :: Vec a m) . List a 

let appendL5 = 
     (\ a n xs m ys ->
                   vecElim a
                           (\n xs -> forall (m :: Nat) (ys :: Vec a m) . List a) 
                           (\m ys -> vectToList a m ys)
                           (\n x xs rec m ys ->                        
                                  LCons a x (rec m ys)) 
                           n xs m ys
     ) :: forall (a :: *) (n :: Nat) (xs :: Vec a n) (m :: Nat) (ys :: Vec a m) . List a 

let appendL6 = 
     (\ a n xs m ys ->
                   vecElim a
                           (\n xs -> forall (m :: Nat) (ys :: Vec a m) . Sigma Nat (\m -> Vec a m) ) 
                           (\m ys -> Pair Nat m (\m -> Vec a m) ys)
                           (\n x xs rec m ys -> 
                                sigElim Nat
                                        (\o -> Vec a o)
                                        (\a' -> Sigma Nat (\o -> Vec a o))
                                        (\o vo -> Pair Nat (Succ o) (\o -> Vec a o) (Cons a o x vo))
                            (rec m ys))
                           n xs m ys
     ) :: forall (a :: *) (n :: Nat) (xs :: Vec a n) (m :: Nat) (ys :: Vec a m) . Sigma Nat (\m -> Vec a m) 

let appendL7 = 
     (\ a n xs m ys ->
                   vecElim a
                           (\n xs -> forall (m :: Nat) (ys :: Vec a m) . Vec a (plus n m)) 
                           (\m ys -> ys)
                           (\n x xs rec m ys -> 
                                (Cons a (plus n m) x (rec m ys)))
                           n xs m ys
     ) :: forall (a :: *) (n :: Nat) (xs :: Vec a n) (m :: Nat) (ys :: Vec a m) . Vec a (plus n m) 