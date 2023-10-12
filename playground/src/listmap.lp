-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ

let map = 
    (\ a b f xs ->
                    listElim a
                             (\xs -> List b) 
                             (LNil b) 
                             (\x xs rec -> LCons b (f x) rec) 
                             xs
    ) :: forall (a :: *) (b :: *) (f :: a -> b) (ls :: List a) . List b 

let map4 = 
    (\ a b f n xs ->
                    vecElim a 
                            (\n xs -> List b)
                            (LNil b)
                            (\n x xs rec -> LCons b (f x) rec)
                            n xs 
    ) :: forall (a :: *) (b :: *) (f :: a -> b) (n :: Nat) (ls :: Vec a n) . List b 

let mapRefactored = (\ x -> \ y -> \ z -> \ a -> \ b -> vecElim y
                                      (\ c -> \ d -> List z)
                                      (LNil z)
                                      (\ c -> \ d -> \ e -> \ f -> LCons z (a d) f)
                                      x
                                      b) :: forall (x :: Nat)
                                                   (y :: *)
                                                   (z :: *)
                                                   (a :: forall a :: y . z)
                                                   (b :: Vec y x) .
                                            List z

let map5 =
    ( \a b f n xs ->
                    vecElim a 
                            (\n xs -> Sigma Nat (\m -> Vec b m))
                            (Pair Nat Zero (\m -> Vec b m) (Nil b) )
                            (\n x xs rec -> sigElim Nat
                                                    (\m -> Vec b m)
                                                    (\a -> Sigma Nat (\m -> Vec b m))
                                                    (\m vm -> Pair Nat (Succ m) (\m -> Vec b m) (Cons b m (f x) vm))
                                                    rec )
                            n xs
    ) :: forall (a :: *) (b :: *) (f :: a -> b) (n :: Nat) (ls :: Vec a n) . Sigma Nat (\m -> Vec b m)

let map6 = 
    ( \a b f n xs ->
                    vecElim a 
                            (\n xs -> Vec b n) 
                            (Nil b)
                            (\m x xs rec -> Cons b m (f x) rec)
                            n xs 
    ) :: forall (a :: *) (b :: *) (f :: a -> b) (n :: Nat) (ls :: Vec a n) .  Vec b n 