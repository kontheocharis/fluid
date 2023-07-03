
-- identity and const
let id    = (\ a x -> x) :: forall (a :: *) . a -> a 
let const = (\ a b x y -> x) :: forall (a :: *) (b :: *) . a -> b -> a

-- addition of natural numbers
let plus =
  natElim
    ( \ _ -> Nat -> Nat )           -- motive
    ( \ n -> n )                    -- case for Zero
    ( \ p rec n -> Succ (rec n) )   -- case for Succ

-- predecessor, mapping 0 to 0
let pred =
  natElim
    ( \ n -> Nat )
    Zero
    ( \ n' _rec -> n' )


-- a simpler elimination scheme for natural numbers
let natFold =
  ( \ m mz ms -> natElim
                   ( \ _ -> m )
                   mz
                   ( \ n' rec -> ms rec ) )
  :: forall (m :: *) . m -> (m -> m) -> Nat -> m

-- an eliminator for natural numbers that has special
-- cases for 0 and 1
let nat1Elim =
  ( \ m m0 m1 ms -> natElim m m0
                            (\ p rec -> natElim (\ n -> m (Succ n)) m1 ms p) )
  :: forall (m :: Nat -> *) . m 0 -> m 1 ->
     (forall n :: Nat . m (Succ n) -> m (Succ (Succ n))) ->
     forall (n :: Nat) . m n

-- an eliminator for natural numbers that has special
-- cases for 0, 1 and 2
let nat2Elim =
  ( \ m m0 m1 m2 ms -> nat1Elim m m0 m1
                                (\ p rec -> natElim (\ n -> m (Succ (Succ n))) m2 ms p) )
  :: forall (m :: Nat -> *) . m 0 -> m 1 -> m 2 ->
     (forall n :: Nat . m (Succ (Succ n)) -> m (Succ (Succ (Succ n)))) ->
     forall (n :: Nat) . m n
-- increment by one
let inc = natFold Nat (Succ Zero) Succ

-- embed Fin into Nat
let finNat = finElim (\ _ _ -> Nat)
                     (\ _ -> Zero)
                     (\ _ _ rec -> Succ rec)

-- unit type
let Unit = Fin 1
-- constructor
let U = FZero 0
-- eliminator
let unitElim =
  ( \ m mu -> finElim ( nat1Elim (\ n -> Fin n -> *)
                                 (\ _ -> Unit)
                                 (\ x -> m x)
                                 (\ _ _ _ -> Unit) )
                      ( natElim (\ n -> natElim (\ n -> Fin (Succ n) -> *)
                                                (\ x -> m x)
                                                (\ _ _ _ -> Unit)
                                                n (FZero n))
                                mu
                                (\ _ _ -> U) )
                      ( \ n f _ -> finElim (\ n f -> natElim (\ n -> Fin (Succ n) -> *)
                                                             (\ x -> m x)
                                                             (\ _ _ _ -> Unit)
                                                             n (FSucc n f))
                                           (\ _ -> U)
                                           (\ _ _ _ -> U)
                                           n f )
                      1 )
  :: forall (m :: Unit -> *) . m U -> forall (u :: Unit) . m u

-- empty type
let Void = Fin 0
-- eliminator
let voidElim =
  ( \ m -> finElim (natElim (\ n -> Fin n -> *)
                            (\ x -> m x)
                            (\ _ _ _ -> Unit))
                   (\ _ -> U)
                   (\ _ _ _ -> U)
                   0 )
  :: forall (m :: Void -> *) (v :: Void) . m v

-- type of booleans 
let Bool = Fin 2 
-- constructors
let False = FZero 1
let True  = FSucc 1 (FZero 0)
-- eliminator
let boolElim =
  ( \ m mf mt -> finElim ( nat2Elim (\ n -> Fin n -> *)
                                    (\ _ -> Unit) (\ _ -> Unit)
                                    (\ x -> m x)
                                    (\ _ _ _ -> Unit) )
                         ( nat1Elim ( \ n -> nat1Elim (\ n -> Fin (Succ n) -> *)
                                                      (\ _ -> Unit)
                                                      (\ x -> m x)
                                                      (\ _ _ _ -> Unit)
                                                      n (FZero n))
                                    U mf (\ _ _ -> U) )
                         ( \ n f _ -> finElim ( \ n f -> nat1Elim (\ n -> Fin (Succ n) -> *)
                                                                  (\ _ -> Unit)
                                                                  (\ x -> m x)
                                                                  (\ _ _ _ -> Unit)
                                                                  n (FSucc n f) )
                                              ( natElim
                                                  ( \ n -> natElim
                                                             (\ n -> Fin (Succ (Succ n)) -> *)
                                                             (\ x -> m x)
                                                             (\ _ _ _ -> Unit)
                                                             n (FSucc (Succ n) (FZero n)) )
                                                  mt (\ _ _ -> U) )
                                              ( \ n f _ -> finElim
                                                             (\ n f -> natElim
                                                                         (\ n -> Fin (Succ (Succ n)) -> *)
                                                                         (\ x -> m x)
                                                                         (\ _ _ _ -> Unit)
                                                                         n (FSucc (Succ n) (FSucc n f)))
                                                             (\ _ -> U)
                                                             (\ _ _ _ -> U)
                                                             n f )
                                              n f )
                         2 )
  :: forall (m :: Bool -> *) . m False -> m True -> forall (b :: Bool) . m b

-- boolean not, and, or, equivalence, xor
let not = boolElim (\ _ -> Bool) True False
let and = boolElim (\ _ -> Bool -> Bool) (\ _ -> False) (id Bool)
let or  = boolElim (\ _ -> Bool -> Bool) (id Bool) (\ _ -> True)
let iff = boolElim (\ _ -> Bool -> Bool) not (id Bool)
let xor = boolElim (\ _ -> Bool -> Bool) (id Bool) not

-- even, odd, isZero, isSucc
let even    = natFold Bool True not
let odd     = natFold Bool False not
let isZero  = natFold Bool True (\ _ -> False)
let isSucc  = natFold Bool False (\ _ -> True)

-- equality on natural numbers
let natEq =
  natElim
    ( \ _ -> Nat -> Bool )
    ( natElim
        ( \ _ -> Bool )
        True
        ( \ n' _ -> False ) )
    ( \ m' rec_m' -> natElim
                       ( \ _ -> Bool )
                       False
                       ( \ n' _ -> rec_m' n' ))

-- "oh so true"
let Prop = boolElim (\ _ -> *) Void Unit

-- reflexivity of equality on natural numbers
let pNatEqRefl =
  natElim
    (\ n -> Prop (natEq n n))
    U
    (\ n' rec -> rec)
  :: forall (n :: Nat) . Prop (natEq n n)

-- alias for type-level negation 
let Not = (\ a -> a -> Void) :: * -> *

-- Leibniz prinicple (look at the type signature)
let leibniz =
  ( \ a b f -> eqElim a
                 (\ x y eq_x_y -> Eq b (f x) (f y))
                 (\ x -> Refl b (f x)) )
  :: forall (a :: *) (b :: *) (f :: a -> b) (x :: a) (y :: a) .
     Eq a x y -> Eq b (f x) (f y)

-- symmetry of (general) equality
let symm =
  ( \ a -> eqElim a
             (\ x y eq_x_y -> Eq a y x)
             (\ x -> Refl a x) )
  :: forall (a :: *) (x :: a) (y :: a) .
     Eq a x y -> Eq a y x

-- transitivity of (general) equality
let tran =
  ( \ a x y z eq_x_y -> eqElim a
                          (\ x y eq_x_y -> forall (z :: a) . Eq a y z -> Eq a x z)
                          (\ x z eq_x_z -> eq_x_z)
                          x y eq_x_y z )
  :: forall (a :: *) (x :: a) (y :: a) (z :: a) .
     Eq a x y -> Eq a y z -> Eq a x z

-- apply an equality proof on two types
let apply =
  eqElim * (\ a b _ -> a -> b) (\ _ x -> x)
  :: forall (a :: *) (b :: *) (p :: Eq * a b) . a -> b

-- proof that 1 is not 0
let p1IsNot0 =
  (\ p -> apply Unit Void
                (leibniz Nat *
                         (natElim (\ _ -> *) Void (\ _ _ -> Unit))
                         1 0 p)
                U)
  :: Not (Eq Nat 1 0)

-- proof that 0 is not 1
let p0IsNot1 =
  (\ p -> p1IsNot0 (symm Nat 0 1 p))
  :: Not (Eq Nat 0 1)

-- proof that zero is not a successor
let p0IsNoSucc = 
  natElim
    ( \ n -> Not (Eq Nat 0 (Succ n)) )
    p0IsNot1
    ( \ n' rec_n' eq_0_SSn' ->
      rec_n' (leibniz Nat Nat pred Zero (Succ (Succ n')) eq_0_SSn') )

-- generate a vector of given length from a specified element (replicate)
let replicate =
  ( natElim
      ( \ n -> forall (a :: *) . a -> Vec a n )
      ( \ a _ -> Nil a )
      ( \ n' rec_n' a x -> Cons a n' x (rec_n' a x) ) )
  :: forall (n :: Nat) . forall (a :: *) . a -> Vec a n

-- generate a vector of given length n, containing the natural numbers smaller than n
let fromto =
  natElim
    ( \ n -> Vec Nat n )
    ( Nil Nat )
    ( \ n' rec_n' -> Cons Nat n' n' rec_n' )

-- append two vectors
let append =
  ( \ a -> vecElim a
             (\ m _ -> forall (n :: Nat) . Vec a n -> Vec a (plus m n))
             (\ _ v -> v)
             (\ m v vs rec n w -> Cons a (plus m n) v (rec n w)))
  ::  forall (a :: *) (m :: Nat) (v :: Vec a m) (n :: Nat) (w :: Vec a n).
      Vec a (plus m n)

let length = 
  (\ a xs -> listElim a 
             (\xs -> Nat)
             Zero 
             (\x xs rec -> plus 1 rec ) xs
  ) :: forall (a :: *) (xs :: List a) . Nat 

let vectToList = 
  ( \ a n xs -> vecElim a 
                        (\n -> List a)
                        (\ _ -> LNil a)
                        (\n xs rec -> LCons a x (rec xs))

  ) :: forall (a :: *) (n :: Nat) (xs :: Vec a n) . List a 

-- helper function for tail, see below
let tail' =
  (\ a -> vecElim a ( \ m v -> forall (n :: Nat) . Eq Nat m (Succ n) -> Vec a n )
                    ( \ n eq_0_SuccN -> voidElim ( \ _ -> Vec a n )
                                                 ( p0IsNoSucc n eq_0_SuccN ) )
                    ( \ m' v vs rec_m' n eq_SuccM'_SuccN ->
                      eqElim Nat
                             (\ m' n e -> Vec a m' -> Vec a n)
                             (\ _ v -> v)
                             m' n
                             (leibniz Nat Nat pred (Succ m') (Succ n) eq_SuccM'_SuccN) vs))
  :: forall (a :: *) (m :: Nat) . Vec a m -> forall (n :: Nat) . Eq Nat m (Succ n) -> Vec a n

-- compute the tail of a vector
let tail =
  (\ a n v -> tail' a (Succ n) v n (Refl Nat (Succ n)))
  :: forall (a :: *) (n :: Nat) . Vec a (Succ n) -> Vec a n

-- projection out of a vector
let at =
  (\ a -> vecElim a ( \ n v -> Fin n -> a )
                    ( \ f -> voidElim (\ _ -> a) f )
                    ( \ n' v vs rec_n' f_SuccN' ->
                      finElim ( \ n _ -> Eq Nat n (Succ n') -> a )
                              ( \ n e -> v )
                              ( \ n f_N _ eq_SuccN_SuccN' ->
                                rec_n' (eqElim Nat
                                               (\ x y e -> Fin x -> Fin y)
                                               (\ _ f -> f)
                                               n n'
                                               (leibniz Nat Nat pred
                                                        (Succ n) (Succ n') eq_SuccN_SuccN')
                                               f_N))
                              (Succ n')
                              f_SuccN'
                              (Refl Nat (Succ n'))))
  :: forall (a :: *) (n :: Nat) . Vec a n -> Fin n -> a

-- head of a vector
let head =
  (\ a n v -> at a (Succ n) v (FZero n))
  :: forall (a :: *) (n :: Nat) . Vec a (Succ n) -> a

-- vector map
let map =
  (\ a b f -> vecElim a ( \ n _ -> Vec b n )
                        ( Nil b )
                        ( \ n x _ rec -> Cons b n (f x) rec ))
  :: forall (a :: *) (b :: *) (f :: a -> b) (n :: Nat) . Vec a n -> Vec b n

-- proofs that 0 is the neutral element of addition
-- one direction is trivial by definition of plus:
let p0PlusNisN =
  Refl Nat
  :: forall n :: Nat . Eq Nat (plus 0 n) n

-- the other direction requires induction on N:
let pNPlus0isN =
  natElim ( \ n -> Eq Nat (plus n 0) n )
          ( Refl Nat 0 )
          ( \ n' rec -> leibniz Nat Nat Succ (plus n' 0) n' rec )
  :: forall n :: Nat . Eq Nat (plus n 0) n

assume (k1 :: Nat)
assume (k2 :: Nat)
assume (z :: Eq Nat k1 k2)
symm

let pp = Eq Nat (plus k1 0) k1
let zz = pNPlus0isN k1 :: pp

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

-- apply3' : (a : Type) -> (x,y : a) -> (p : a -> Type) -> x = y -> p x -> p y
-- apply3' a x y p p2 px = 
--  eqElim a 
--         (\x, y, _ => p x -> p y) 
--         (\ _, x => x) x y p2 px

let apply3 =
 (\a x y p p2 px ->
    eqElim a 
           (\x y _ -> p x -> p y)
           (\_ x -> x) x y p2 px
 ) :: forall (a :: *) (x :: a) (y :: a) (p :: a -> *) (p2 :: Eq a x y) . p x -> p y

let antisym = 
 (\m n p -> lteElim (\m n _ -> forall (p' :: LTE n m) . Eq Nat m n)
                    (\n e -> lteElim (\n m _ -> forall (p :: Eq Nat m Zero) . Eq Nat m n)
                             (\n e -> e)
                             (\k l _ _ e -> voidElim (\_ -> Eq Nat (Succ l) (Succ k))
                                                     (noConf (Succ l) Zero e))
                              n Zero e (Refl Nat Zero)
                    ) 
                    (\m n _ h q -> leibniz Nat Nat Succ n m (
                           h (
                              lteElim (\k l _ -> forall (p1 :: Eq Nat k (Succ n)) (p2 :: Eq Nat l (Succ m)) . LTE n m)
                                      (\_ e _ -> voidElim (\_ -> LTE n m) (noConf Zero (Succ n) e))
                                      (\k l e _ x y -> apply3 Nat k n (\n -> LTE n m) (noConf (Succ k) (Succ n) x) (apply3 Nat l m (\m -> LTE k m) (noConf (Succ l) (Succ m) y) e)) 
                                      (Succ n) (Succ m) q (Refl Nat (Succ n)) (Refl Nat (Succ m))
                           )))                 
 )
   :: forall (m :: Nat) (n :: Nat) (p :: LTE n m) . Eq Nat m n 