-- from prelude
-- proof that zero is not a successor
let p0IsNoSucc = 
  natElim
    ( \ n -> Not (Eq Nat 0 (Succ n)) )
    p0IsNot1
    ( \ n' rec_n' eq_0_SSn' ->
      rec_n' (leibniz Nat Nat pred Zero (Succ (Succ n')) eq_0_SSn') )


let NoConfusion = 
  (\ x y ->
           natElim (\x -> forall (y :: Nat) . *) 
                   (\y -> natElim (\y -> *) 
                                  (Eq Nat Zero Zero)
                                  (\m t -> Void) 
                                  y )
                   ( \ n hyp sm -> natElim (\y -> *)
                                           Void 
                                           (\m t -> Eq Nat n m)
                                           sm) x y
  ) :: forall (x :: Nat) (y :: Nat) . *

let noConf = 
  (\ x y p ->
        natElim (\x -> forall (y :: Nat) (p :: Eq Nat x y) . NoConfusion x y)
                (\y p0ey -> natElim (\y -> forall (p :: Eq Nat Zero y) . NoConfusion Zero y)
                                    (\p -> Refl Nat Zero)
                                    (\z hyp p -> p0IsNoSucc z p) y p0ey)
                (\sx hyp y p -> natElim (\y -> forall (p :: Eq Nat (Succ sx) y) . NoConfusion (Succ sx) y)
                                        (\p -> p0IsNoSucc sx (symm Nat (Succ sx) Zero p))
                                        (\z hyp p -> leibniz Nat Nat pred (Succ sx) (Succ z) p) y p) x y p
  ) :: forall (x :: Nat) (y :: Nat) (p :: Eq Nat x y) . NoConfusion x y

let fromLteSucc2 = 
 ( \ n m p ->
       lteElim (\k l _ -> Eq Nat k (Succ n) -> Eq Nat l (Succ m) -> LTE n m)
               (\_ e _ -> voidElim (\_ -> LTE n m) (noConf Zero (Succ n) e))
               (\k l e _ x y -> apply3 Nat k n (\n -> LTE n m) (noConf (Succ k) (Succ n) x) (apply3 Nat l m (\m -> LTE k m) (noConf (Succ l) (Succ m) y) e))
               (Succ n) (Succ m) p (Refl Nat (Succ n)) (Refl Nat (Succ m))

 ) :: forall (n :: Nat) (m :: Nat) (p :: LTE (Succ n) (Succ m)) . LTE n m 

-------------------------------------

let index0 =
    ( \a i xs ->
           listElim a
                    (\l -> forall (i :: Nat) . Maybe a)
                    (\i -> Nothing a)
                    (\x xs rec i -> 
                        natElim (\i -> Maybe a)
                                (Just a x)
                                (\i' recN -> rec i') i
                    ) xs i 

    ) :: forall (a :: *) (i :: Nat) (xs :: List a) . Maybe a



let index1 =
    ( \a i n xs ->
           vecElim a
                    (\n l -> forall (i :: Nat) . Maybe a)
                    (\i -> Nothing a)
                    (\n' x xs rec i -> 
                        natElim (\i -> Maybe a)
                                (Just a x)
                                (\i' recN -> rec i') i
                    ) n xs i 

    ) :: forall (a :: *) (i :: Nat) (n :: Nat) (xs :: Vec a n) . Maybe a

let index1Refactored = (\ x -> \ y -> \ z -> \ a -> vecElim y
                               (\ b -> \ c -> forall d :: Nat . Maybe y)
                               (\ b -> Nothing y)
                               (\ b -> \ c -> \ d -> \ e -> \ f -> natElim (\ g -> Maybe y)
                                                                     (Just y c)
                                                                     (\ g -> \ h -> e g)
                                                                     f)
                               x
                               a
                               z) :: forall (x :: Nat) (y :: *) (z :: Nat) (a :: Vec y x) .
                                     Maybe y


let index2 = 
    (\ a i n xs p ->
           vecElim a
                    (\n l -> forall (i :: Nat) (p :: LTE (Succ i) n). Maybe a)
                    (\i p -> Nothing a)
                    (\n' x xs rec i p2 -> 
                        natElim (\i -> forall (p :: LTE (Succ i) (Succ n')) . Maybe a)  -- how to know Succ n'?
                                (\p -> Just a x)
                                (\i' recN p3 -> 
                                        lteElim (\l r p -> Maybe a)
                                                (\ssi -> rec i' (fromLteSucc2 (Succ i') n' p3))
                                                (\l r p4 recL -> rec i' (fromLteSucc2 (Succ i') n' p3))
                                                (Succ (Succ i')) (Succ n') p3) i p2
                    ) n xs i p

    ) :: forall (a :: *) (i :: Nat) (n :: Nat) (xs :: Vec a n) (p :: LTE (Succ i) n) . Maybe a 

let index4 = 
    (
        \a i n xs p -> 
                       vecElim a
                    (\n l -> forall (i :: Nat) (p :: LTE (Succ i) n). Maybe a)
                    (\i p -> voidElim (\_ -> Maybe a) (p0IsNoSucc i (antisym Zero (Succ i) (LTEZero (Succ i)) p)))
                    (\n' x xs rec i p2 -> 
                        natElim (\i -> forall (p :: LTE (Succ i) (Succ n')) . Maybe a)  -- how to know Succ n'?
                                (\p -> Just a x)
                                (\i' recN p3 -> 
                                        lteElim (\l r p -> Maybe a)
                                                (\ssi -> rec i' (fromLteSucc2 (Succ i') n' p3))
                                                (\l r p4 recL -> rec i' (fromLteSucc2 (Succ i') n' p3))
                                                (Succ (Succ i')) (Succ n') p3) i p2
                    ) n xs i p
    ) :: forall (a :: *) (i :: Nat) (n :: Nat) (xs :: Vec a n) (p :: LTE (Succ i) n) . Maybe a 

let index5 = 
    (
        \a i n xs p -> 
                       vecElim a
                    (\n l -> forall (i :: Nat) (p :: LTE (Succ i) n). a)
                    (\i p -> voidElim (\_ -> a) (p0IsNoSucc i (antisym Zero (Succ i) (LTEZero (Succ i)) p)))
                    (\n' x xs rec i p2 -> 
                        natElim (\i -> forall (p :: LTE (Succ i) (Succ n')) . a)  -- how to know Succ n'?
                                (\p -> x)
                                (\i' recN p3 -> 
                                        lteElim (\l r p -> a)
                                                (\ssi -> rec i' (fromLteSucc2 (Succ i') n' p3))
                                                (\l r p4 recL -> rec i' (fromLteSucc2 (Succ i') n' p3))
                                                (Succ (Succ i')) (Succ n') p3) i p2
                    ) n xs i p
    ) :: forall (a :: *) (i :: Nat) (n :: Nat) (xs :: Vec a n) (p :: LTE (Succ i) n) . a 
