import Data.Nat
import Data.Fin
import Data.Vect
import Decidable.Equality
import RefacPrelude


listConcat: (a: Type) -> List a -> List a -> List a 
listConcat a list1 list2 = listElim a 
                                    (\x=> List a) 
                                    list2 
                                    (\x,xs, xsRes => (x::xsRes) ) 
                                    list1


-- listConcat Nat []  [1,2,3]
-- listConcat Nat [1,2,3] []  
-- listConcat Nat [1,2,3] [1,2,3]


vectConcat: (a: Type) -> (len1:Nat) -> (len2:Nat) -> 
               Vect len1 a -> 
               Vect len2 a ->  
               Vect (len1 + len2) a 
vectConcat a len1 len2 vec1 vec2 = 
    vecElim  a 
            (\m,v => (Vect len2 a -> Vect (m + len2) a ))  
            (\v2 => v2)
            (\tailLen, x, xs, combineWithV2 => (\v2 =>  x::(combineWithV2 v2)) )
            len1
            vec1
            vec2


-- vectConcat Nat 0 3 [] [1,2,3]
-- vectConcat Nat 3 0 [1,2,3] []
-- vectConcat Nat 3 4 [1,2,3] [1,2,3,4]

-------------------------------------------------------------------------------

reverse0 :  (a: Type) ->  List a -> List a
reverse0 a l = listElim a 
                        (\x=> List a) 
                        ([] ) 
                        (\x,xs, xsRes => listConcat a xsRes [x]  ) 
                        l


-- reverse0 Nat [] 
-- reverse0 Nat [1,2,3,4]

-------------------------------------------------------------------------------

reverse1 :  (a: Type) -> (m:Nat) -> Vect m a -> List a
reverse1 a m vec = 
    vecElim  a 
            (\n,v => List a) 
            ([])
            (\n,x,xs,xsRes => listConcat a 
                                          xsRes 
                                          [x] ) 
            m vec

-- reverse1 Nat Z []
-- reverse1 Nat 4 [1,2,3,4]

-------------------------------------------------------------------------------

reverse2 :  (a: Type) -> (m:Nat) -> Vect m a -> (k : Nat ** Vect k a) 
reverse2 a m vec = 
    vecElim  a 
            (\n,v => (k : Nat **  Vect k a)) 
            (Z ** []) 
            (\n,x,xs,(l**rres) => ( (l+1) ** ( vectConcat a l (S Z) 
                                                            rres 
                                                            [x] ) ) ) 
            m vec


-- reverse2 Nat Z []
-- reverse2 Nat 4 [1,2,3,4]

-- TODO: use projection for dep pair
-------------------------------------------------------------------------------

{-
reverse3x : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: k=m) -> (Vect k a) 
reverse3x a m vec k pf = 
        vecElim a 
                (\n,v => Vect n a) 
                ([]) 
                (\n,x,xs,rres => (rewrite (plusCommutative 1 n)  in
                                        (vectConcat a n (S Z) 
                                                      rres 
                                                      [x] ) ) ) 
                k 
                --(rewrite pf in vec)
                (let vectPf = leibnitz Nat Type (\n => Vect n a) k m pf  in 
                    (myEqElim Type (\v1,v2,pf=>v1) (\v => ?vec) (Vect k a ) (Vect m a) vectPf)
                )

 -}              
--(myEqElim (Vect m a) (\v1, v2, pf => v2) (\v => ?rewrittenTo) vec ?vec ?ppf )--(leibnitz Nat Type (\n => Vect n a) k m pf) )
                

-- reverse3x Nat Z [] Z Refl
-- reverse3x Nat 4 [1,2,3,4] 4 Refl
     

-------------------------------------------------------------------------------

{-
reverse30x : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: k=m) -> (Vect k a) 
reverse30x a m vec k pf = 
        vecElim a 
                (\n,v => Vect n a) 
                ([]) 
                (\n,x,xs,rres => (rewrite (plusCommutative 1 n)  in
                                        (vectConcat a n (S Z) 
                                                      rres 
                                                      [x] ) ) ) 
                k   
                --(rewrite pf in vec)            
                (test a m vec k pf ) where 
                        test: (a:Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: k=m) -> (Vect k a) 
                        test a m vec k pf = --(rewrite pf in vec)
                                natElim (\n => Vect k a) 
                                        (case pf of 
                                                Refl => vec) 
                                        (case pf of 
                                                Refl => (\pred, rres => rres) ) 
                                        m
                                --case m of 
                                --        Z => case pf of 
                                --                Refl => vec
                                --        S n => case pf of 
                                --                Refl => vec 
                                --TODO use natElim              

-- reverse30x Nat Z [] Z Refl
-- reverse30x Nat 4 [1,2,3,4] 4 Refl

-------------------------------------------------------------------------------


reverse31x : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: k=m) -> (Vect k a) 
reverse31x a m vec k pf = 
        vecElim a 
                (\n,v => Vect n a) 
                ([]) 
                (\n,x,xs,rres => (rewrite (plusCommutative 1 n)  in
                                        (vectConcat a n (S Z) 
                                                      rres 
                                                      [x] ) ) ) 
                k               
                (test a m vec k pf ) where 
                        test: (a:Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: k=m) -> (Vect k a) 
                        test a m vec k pf = --(rewrite pf in vec)
                                case pf of Refl => natElim (\n => Vect m a) 
                                                           (vec) 
                                                           (\pred, rres => rres ) 
                                                           m          
                                        

-- reverse31x Nat Z [] Z Refl
-- reverse31x Nat 4 [1,2,3,4] 4 Refl


-------------------------------------------------------------------------------


reverse32 : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a) 
reverse32 a m vec k pf = 
        vecElim a 
                (\n,v => Vect n a) 
                ([]) 
                (\n,x,xs,rres => (rewrite (plusCommutative 1 n)  in
                                        (vectConcat a n (S Z) 
                                                      rres 
                                                      [x] ) ) ) 
                m               
                (eqElim  Nat 
                        (\l,l',p => Vect l a) 
                        (\l => (natElim (\n => Vect n a) 
                                        ([]) 
                                        (\pred, rres => ?rres ) 
                                        l   ) )
                        m 
                        k
                        pf   )
                             
                                                
                                          

-- reverse32 Nat Z [] Z Refl
-- reverse32 Nat 4 [1,2,3,4] 4 Refl

-}


-------------------------------------------------------------------------------


reverse30 : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: k=m) -> (Vect k a) 
reverse30 a m vec k pf = 
        vecElim a 
                (\n,v => Vect n a) 
                ([]) 
                (\n,x,xs,rres => (rewrite (plusCommutative 1 n)  in
                                        (vectConcat a n (S Z) 
                                                      rres 
                                                      [x] ) ) ) 
                k               
                (test a m vec k pf ) where 
                        test: (a:Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: k=m) -> (Vect k a) 
                        test a m vec k pf = --(rewrite pf in vec)
                                        case pf of Refl => natElim (\n => Vect k a) 
                                                                (vec) 
                                                                (\pred, rres => rres )   --essentially we have f(3) = f(2) = f(1) = f(0) = vec ...feels like cheating
                                                                m                        -- since Refl, m will unify with k

-- reverse30 Nat Z [] Z Refl
-- reverse30 Nat 4 [1,2,3,4] 4 Refl

-------------------------------------------------------------------------------

reverse31 : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: k=m) -> (Vect k a) 
reverse31 a m vec k pf = case pf of  
                                Refl => (vecElim a 
                                        (\n,v => Vect n a) 
                                        ([]) 
                                        (\n,x,xs,rres => (rewrite (plusCommutative 1 n)  in
                                                                (vectConcat a n (S Z) 
                                                                        rres 
                                                                        [x] ) ) ) 
                                        k               
                                        vec)


-- reverse31 Nat Z [] Z Refl
-- reverse31 Nat 4 [1,2,3,4] 4 Refl

-------------------------------------------------------------------------------

reverse32 : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: k=m) -> (Vect k a) 
reverse32 a m vec k pf = case pf of  
                                Refl => (vecElim a 
                                        (\n,v => Vect n a) 
                                        ([]) 
                                        (\n,x,xs,rres => (rewrite (plusCommutative 1 n)  in
                                                                (vectConcat a n (S Z) 
                                                                        rres 
                                                                        [x] ) ) ) 
                                        k               
                                        vec)


-- reverse32 Nat Z [] Z Refl
-- reverse32 Nat 4 [1,2,3,4] 4 Refl



--

myRewrite : (f : a -> Type) -> x = y -> f y -> f x
myRewrite f Refl prf = prf

myApply2 : (a : Type) -> (b : Type) -> (p : a = b) -> a -> b
myApply2 =
  eqElim Type (\ a, b, _ => a -> b) (\ _  =>  (\x => x))



test0: (a:Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a) 
test0 a m vec k pf = let eqTypePf = (leibniz Nat Type (\n => Vect n a) m k pf) in 
                        (myApply2 (Vect m a) (Vect k a) eqTypePf vec)


------------------------------  

test01: (a:Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a) 
test01 a m vec k pf = myApply2  (Vect m a) 
                                (Vect k a) 
                                (leibniz Nat Type 
                                         (\n => Vect n a) 
                                         m k pf)
                                vec



reverse301 : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a) 
reverse301 a m vec k pf = 
        vecElim a 
                (\n,v => Vect n a) 
                ([]) 
                (\n,x,xs,rres => (rewrite (plusCommutative 1 n)  in
                                        (vectConcat a n (S Z) 
                                                      rres 
                                                      [x] ) ) ) 
                k 
                --(rewrite pf in vec)
                (test01 a m vec k pf )


-- reverse301 Nat Z [] Z Refl
-- reverse301 Nat 4 [1,2,3,4] 4 Refl

------------------------------  

test02: (a:Type) -> (m:Nat) -> Vect (Prelude.plus m 1) a  -> Vect (Prelude.plus 1 m) a
test02 a m vec = myApply2  (Vect (Prelude.plus m 1) a) 
                           (Vect (Prelude.plus 1 m) a) 
                           (leibniz Nat Type 
                                         (\n => Vect n a) 
                                         (Prelude.plus m 1) 
                                         (Prelude.plus 1 m) 
                                         (plusCommutative m 1))
                           vec



reverse302 : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a) 
reverse302 a m vec k pf = 
        vecElim a 
                (\n,v => Vect n a) 
                ([]) 
                (\n,x,xs,rres => ( test02 a n 
                                          (vectConcat a n (S Z) 
                                                      rres 
                                                      [x] ) 
                                                      ) ) 
                k 
                (test01 a m vec k pf )


-- reverse302 Nat Z [] Z Refl
-- reverse302 Nat 4 [1,2,3,4] 4 Refl

-------------------------------------------------------------------

reverse3 : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a) 
reverse3 a m vec k pf = 
        vecElim a 
                (\n,v => Vect n a) 
                ([]) 
                (\n,x,xs,rres => myApply2  (Vect (Prelude.plus n 1) a) 
                                           (Vect (Prelude.plus 1 n) a) 
                                           (leibniz Nat Type 
                                                    (\n' => Vect n' a) 
                                                    (Prelude.plus n 1) 
                                                    (Prelude.plus 1 n) 
                                                    (plusCommutative n 1))
                                           (vectConcat a n (S Z) 
                                                        rres 
                                                        [x] ) ) 
                k 
                (apply2  (Vect m a) 
                           (Vect k a) 
                           (leibniz Nat Type 
                                    (\n => Vect n a) 
                                    m k pf)
                           vec)

-- reverse3 Nat Z [] Z Refl
-- reverse3 Nat 4 [1,2,3,4] 4 Refl

-------------------------------------------------------------------



natEqnatplusZ : (n:Nat) -> (n = Prelude.plus n Z)
natEqnatplusZ Z = Refl
natEqnatplusZ (S m ) = leibniz Nat 
                               Nat 
                               (\l => S l)
                               m 
                               (Prelude.plus m 0)
                               (natEqnatplusZ m)
--TODO use natelim


test010: (a:Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: k=m) -> (Vect k a) 
test010 a m vec k pf = myApply2  (Vect m a) 
                                (Vect k a) 
                                (leibniz Nat Type 
                                         (\n => Vect n a) 
                                         m k 
                                         (sym pf))
                                vec




plusComm1: (left:Nat) -> (right:Nat) -> (Prelude.plus left right = Prelude.plus right left)
--plusComm1 left right = natElim (\l => (RefacPrelude.plus left right = RefacPrelude.plus right left))
--                              (?nilcase)
--                              (?reccase )
--                               left
--plusComm1 0 right = ?lZ -- rewrite plusZeroRightNeutral right in ?lZ  --we need right = plus right 0, but we have Refl: right = right. so we rewrite r+0 to r
plusComm1 0 right = apply2 (right = right)  
                          (right = Prelude.plus right 0)
                           (leibniz Nat 
                                    Type
                                    (\x => (right = x)) 
                                    right  
                                    (Prelude.plus right 0) 
                                    (natEqnatplusZ right)
                                     ) 
                           Refl                        
--plusComm1 (S m)  right = rewrite (plusComm1 m right) in    --(S (m+r) = S (r+m))
--                                rewrite (plusSuccRightSucc right m) in Refl  --(S (r+m) = r + (S m)) then we have (r + (S m) = r + (S m)) so can put in Refl
plusComm1 (S m)  right = ?aply


plusComm2: (left:Nat) -> (right:Nat) -> (Prelude.plus left right = Prelude.plus right left)
plusComm2 0 right = apply2 (right = right)  
                          (right = Prelude.plus right 0)
                           (leibniz Nat 
                                    Type
                                    (\x => (right = x)) 
                                    right  
                                    (Prelude.plus right 0) 
                                    (natEqnatplusZ right)
                                     ) 
                           Refl                        
plusComm2 (S m) right = rewrite (plusComm2 m right) in    
                                (apply2 (Prelude.plus right (S m) = Prelude.plus right (S m)) 
                                        (S (Prelude.plus right m)= Prelude.plus right (S m))
                                        (leibniz (Nat)
                                                 (Type)
                                                 (\l => l = (right + S m) )
                                                 (Prelude.plus right (S m))
                                                 (S (Prelude.plus right m ))
                                                 (sym (plusSuccRightSucc right m)))                                    
                                        Refl 
                                )
                                --rewrite (plusSuccRightSucc right m) in Refl 



plusComm3: (left:Nat) -> (right:Nat) -> (Prelude.plus left right = Prelude.plus right left)
plusComm3 0 right = apply2 (right = right)  
                          (right = Prelude.plus right 0)
                           (leibniz Nat 
                                    Type
                                    (\x => (right = x)) 
                                    right  
                                    (Prelude.plus right 0) 
                                    (natEqnatplusZ right)
                                     ) 
                           Refl                        
plusComm3 (S m) right = --rewrite (plusComm3 m right) in    
                        apply2  (S (Prelude.plus right m)= Prelude.plus right (S m))
                                ( S (Prelude.plus m right) = Prelude.plus right (S m))
                                (leibniz(Nat)
                                        (Type)
                                        (\l => S l = (right + S m) )
                                        (Prelude.plus right m)
                                        (Prelude.plus m right)
                                        (sym (plusComm3 m right)) ) 
                                (apply2 (Prelude.plus right (S m) = Prelude.plus right (S m)) 
                                        (S (Prelude.plus right m)= Prelude.plus right (S m))
                                        (leibniz (Nat)
                                                 (Type)
                                                 (\l => l = (right + S m) )
                                                 (Prelude.plus right (S m))
                                                 (S (Prelude.plus right m ))
                                                 (sym (plusSuccRightSucc right m)))                                    
                                        Refl 
                                )
                                

--rewrite (plusComm1 m right) in                               
--(S (m+r) = S (r+m))

natEqNatPlusZ : (n:Nat) -> (n = RefacPrelude.plus n Z)
natEqNatPlusZ n = natElim (\l => (l = RefacPrelude.plus l Z))
                          Refl 
                          (\m,recRes => (leibniz Nat 
                                                Nat 
                                                (\l => S l)
                                                m 
                                                (RefacPrelude.plus m 0)
                                                recRes)) 
                          n


succPlusIsPlusSucc : (left, right : Nat) -> S (RefacPrelude.plus left right) = RefacPrelude.plus left (S right)
succPlusIsPlusSucc Z _ = Refl
succPlusIsPlusSucc (S left) right = rewrite succPlusIsPlusSucc left right in Refl                 


plusComm: (left:Nat) -> (right:Nat) -> (RefacPrelude.plus left right = RefacPrelude.plus right left)
plusComm left right = natElim  (\l => (RefacPrelude.plus l right = RefacPrelude.plus right l))
                                (apply2 (right = right)   --base case
                                (right = RefacPrelude.plus right 0)
                                (leibniz Nat 
                                        Type
                                        (\x => (right = x)) 
                                        right  
                                        (RefacPrelude.plus right 0) 
                                        (natEqNatPlusZ right)
                                        ) 
                                Refl)     
                                (\m, recSoln => (apply2 (S (RefacPrelude.plus right m)= RefacPrelude.plus right (S m))
                                                        ( S (RefacPrelude.plus m right) = RefacPrelude.plus right (S m))
                                                        (leibniz(Nat)
                                                                (Type)
                                                                (\l => S l = (RefacPrelude.plus right (S m)) )
                                                                (RefacPrelude.plus right m)
                                                                (RefacPrelude.plus m right)
                                                                (sym recSoln )) 
                                                        (apply2 (RefacPrelude.plus right (S m) = RefacPrelude.plus right (S m)) 
                                                                (S (RefacPrelude.plus right m)= RefacPrelude.plus right (S m))
                                                                (leibniz (Nat)
                                                                        (Type)
                                                                        (\l => l = (RefacPrelude.plus right (S m)) )
                                                                        (RefacPrelude.plus right (S m))
                                                                        (S (RefacPrelude.plus right m ))
                                                                        (sym (succPlusIsPlusSucc right m)))                                    
                                                                Refl )))
                                left




                       





----------------------


reverse310 : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a) 
reverse310 a m vec k pf = 
        vecElim a 
                (\n,v => Vect n a) 
                ([]) 
                (\n,x,xs,rres => myApply2  (Vect (Prelude.plus n 1) a) 
                                           (Vect (Prelude.plus 1 n) a) 
                                           (leibniz Nat Type 
                                                    (\n' => Vect n' a) 
                                                    (Prelude.plus n 1) 
                                                    (Prelude.plus 1 n) 
                                                    (plusCommutative n 1))
                                           (vectConcat a n (S Z) 
                                                        rres 
                                                        [x] ) ) 
                k 
                (apply2  (Vect m a) 
                         (Vect k a) 
                         (leibniz Nat Type 
                                  (\n => Vect n a) 
                                  m k pf)
                         vec)

-- reverse310 Nat Z [] Z Refl
-- reverse3 Nat 4 [1,2,3,4] 4 Refl
