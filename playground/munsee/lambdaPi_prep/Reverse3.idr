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
-------------------------------------------------------------------------------

data DepPair: (ty1: Type) -> (term2Calc: ty1 -> Type) ->  Type  where
     MkDepPair: (ty1: Type) -> (term2Calc: ty1 -> Type) ->  (term1 : ty1)  -> (term2: (term2Calc term1)) -> DepPair ty1 term2Calc
     

getDependee: (DepPair ty1 term2Calc) -> ty1
getDependee pair = case pair of (MkDepPair ty1 term2Calc term1 term2) => term1 
--getDependee (MkDepPair Nat 3 (\n => Vect n Nat) [2,3,4])


getDependant: (pair: DepPair ty1 term2Calc) -> term2Calc (getDependee pair)
getDependant pair = case pair of (MkDepPair ty1 term2Calc term1 term2) => term2
--getDependant (MkDepPair Nat 3 (\n => Vect n Nat) [2,3,4])
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

{-
We want to change List to Vect.
We know that we can get vect from list by indexing length, otherwise the constructors are the same
Similarly from Vect to List we drop the index.
the composition of both should give the identity map 
-}


{-
We can add param for len of input, but we do not know the resulting length
User must tell us what is the final length. In this case, equal to the input length
We add this constraint as a param, we would need to use it 

So the goal is something of type  (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a)
-}

{-
1) We first change input list to input vect
2) change return type to dep pair
3) use input pf to eliminate sigma
-}

-------------------------------------------------------------------------------
--Step 1 is relatively strighforward

reverse1 :  (a: Type) -> (m:Nat) -> Vect m a -> List a
reverse1 a m vec = 
    vecElim  a 
            (\n,v => List a) 
            ([])
            (\n,x,xs,xsRes => listConcat a 
                                         xsRes 
                                         [x] ) 
            m 
            vec

-------------------------------------------------------------------------------
--Step 2:
-- by the end we want something of type (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )

--we first change the retTyCalc of vecElim
--for base case, just change list to dep pair
reverse21 :  (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )
reverse21 a m vec = 
    vecElim  a 
             (\n,v => DepPair Nat (\n => Vect n a)) 
             (MkDepPair Nat (\n => Vect n a) Z [])
             ?rev21_recCase
             --(\n,x,xs,xsRes => listConcat a 
             --                            xsRes 
             --                            [x] ) 
             m
             vec

--now the recCase needs to change: the input xsRes and the output is now dep pair
--try to keep right hand side, but it's calling another function, and the types don't match now
--so we need to refactor listConcat to get something of type (a: Type) -> (dp1: DepPair Nat (\n => Vect n a)) -> List a -> DepPair Nat (\n => Vect n a) 
--note the second vec is a list. in the reccase of vecelim, the second list is still a list. 
--there are no reason to change to the concatenation to 2 dps.

----refactor listConcat
vectDPConcat0: (a: Type) -> List a -> List a -> List a 
vectDPConcat0 a list1 list2 = listElim a 
                                    (\l=> List a) 
                                    list2 
                                    (\x,xs, xsRes => (x::xsRes) ) 
                                    list1

--step1: change input type
--Q: how to eliminate dep pair? in the same way that we eliminate list and vec?
--So we need a way of relating the eliminators if lists to elims of vectdps

vectDPConcat1: (a: Type) -> (dp1: DepPair Nat (\n => Vect n a)) -> List a -> List a 
vectDPConcat1 a dp1 list2 = vecElim a 
                                    (\n,v=> List a) 
                                    list2 
                                    (\n,x,xs,xsRes => x::xsRes) 
                                    (getDependee dp1)
                                    (getDependant dp1)

--step2: change output type 
--retTyCalc: just put dp
--basecase: change list to dp
--in reccase, now xsRes is a dp, xs is vect
--use getDependnat to extract data from xsRes, and change listcons to vectcons, also need to make dp
listToVect : (a:Type) -> (xs : List a) -> (DepPair Nat (\m => Vect m a) )
listToVect a []  =  MkDepPair Nat (\m => Vect m a) Z []
listToVect a (x::xs) = MkDepPair Nat (\m => Vect m a) 
                                 (S (getDependee (listToVect a xs)) )  
                                 (x::(getDependant (listToVect a xs)))



vectDPConcat2: (a: Type) -> (dp1: DepPair Nat (\n => Vect n a)) -> List a -> DepPair Nat (\n => Vect n a) 
vectDPConcat2 a dp1 list2 = vecElim a 
                                    (\n,v=> DepPair Nat (\n => Vect n a) ) 
                                    (listToVect a list2)
                                    (\n,x,xs,xsRes => MkDepPair Nat (\m => Vect m a) 
                                                                (S (getDependee xsRes)) 
                                                                (x::(getDependant xsRes))) 
                                    (getDependee dp1)
                                    (getDependant dp1)


--[END]--refactor listConcat

vectDPConcat: (a: Type) -> (dp1: DepPair Nat (\n => Vect n a)) -> List a -> DepPair Nat (\n => Vect n a) 
vectDPConcat a dp1 list2 = vectDPConcat2 a dp1 list2 


reverse22 :  (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )
reverse22 a m vec = 
    vecElim  a 
             (\n,v => DepPair Nat (\n => Vect n a)) 
             (MkDepPair Nat (\n => Vect n a) Z [])
             (\n,x,xs,xsRes => vectDPConcat a 
                                         xsRes 
                                         [x] ) 
             m
             vec

-------------------------------------------------------------------------------
--Step 3: add proof and change ret type

--what should the ret type be? function?
--choice: nat elim or = elim on base case?

xvectfuncConcat:  (a: Type) -> (nnn:Nat) -> (xsRes: ((k':Nat) -> (pf: n=k') -> Vect k' a)) -> (kk : Nat)-> (p:S nnn = kk) -> List a -> Vect kk a 


xreverse31 :  (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) ->  (pf: m=k) -> Vect k a
xreverse31 a m vec k pf= 
    vecElim  a 
             (\n,v => ( (k':Nat) -> (pf: n=k') -> Vect k' a)) 
             (\k', p => case k' of
                              Z => []
                              S l impossible)
             (\nnn,x,xs,xsRes => (\kk, p => xvectfuncConcat a nnn xsRes kk p [x] ) )
                                    --vectDPConcat a 
                                     --    xsRes 
                                     --    [x] ) 
             m
             vec
             k pf

----refactor vectDPConcat

xvectfuncConcat0: (a: Type) -> (dp1: DepPair Nat (\n => Vect n a)) -> List a -> DepPair Nat (\n => Vect n a) 
xvectfuncConcat0 a dp1 list2 = vecElim a 
                                    (\n,v=> DepPair Nat (\n => Vect n a) ) 
                                    (listToVect a list2)
                                    (\n,x,xs,xsRes => MkDepPair Nat (\m => Vect m a) 
                                                                (S (getDependee xsRes)) 
                                                                (x::(getDependant xsRes))) 
                                    (getDependee dp1)
                                    (getDependant dp1)

--add things into contexts
--add params
--change input type
--this requires us to know how to transform dpvecs to ((k':Nat) -> (pf: n=k') -> Vect k' a)!!!  

xvectfuncConcat1: (a: Type) -> (nnn:Nat)  -> (xsRes: ((k':Nat) -> (pf: n=k') -> Vect k' a)) 
                     -> (kk : Nat) -> (p:S nnn = kk)  -> List a -> DepPair Nat (\n => Vect n a) 
xvectfuncConcat1 a nnn xsRes kk p list2 = 
    vecElim a 
            (\n,v=> DepPair Nat (\n => Vect n a) ) 
            (listToVect a list2)
            (\n,x,xs,xsRes => MkDepPair Nat (\m => Vect m a) 
                                        (S n) 
                                        (x::xs)) 
            nnn
            (xsRes nnn ?pp)

--[END]--refactor vectDPConcat
--xvectfuncConcat:  (a: Type) -> (nnn:Nat) -> (xsRes: ((k':Nat) -> (pf: n=k') -> Vect k' a)) -> (kk : Nat)-> (p:S nnn = kk) -> List a -> Vect kk a 

{-
   k : Nat
   m : Nat
   pf : m = k
   a : Type
   vec : Vect m a
   nnn : Nat
   x : a
   xs : Vect nnn a
   xsRes : (k' : Nat) -> nnn = k' -> Vect k' a
   kk : Nat
   p : S nnn = kk
------------------------------
tt2 : Vect kk a
-}


{-
reverse324a :  (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a)
reverse324a a m vec k pf = 
    vecElim  a 
             (\m,vec => ( (k:Nat) -> (pf: m=k) -> Vect k a)) 
             (\k, pf => case pf of Refl => [] )          
             (\m, x, xs, xsRes => (\k, pf =>  --pf: S m = k
                                       case k of 
                                            Z impossible -- S m = Z
                                            (S n) => let pf' = plusLeftCancel 1 m n pf  
                                                        in let recResVec = (xsRes n pf') --Q: how do we know to do this
                                                            in let concat = vectConcat a n (getDependee (listToVect a [x])) recResVec (getDependant (listToVect a [x]))
                                                               in rewrite (plusCommutative 1 n) in concat )   )      
            --                                    vectDPConcat  a 
             --                                   xsRes
             --                                   (listToVect a [x]))
              m 
              vec  
              k pf
-}


vectConcatxx: (a: Type) -> (m:Nat) -> Vect m a -> List a  -> Vect (S m) a  
--how do we infer that the S in the return type correspod to the special case of [x] input?
--this is wrong. Here List a can be of any length so we won't be getting Vect (S m) a -- TODO:  maybe should just put Vect and x as input and always get Vect (S m) a
--we need user to guide us
-- as before, put in input 

vectConcatxxx: (a: Type) -> (m:Nat) -> Vect m a -> List a  -> (l:Nat) -> (pf: l = S m) -> Vect l a  
--this is not enough, the list can still be anything, we should change that to Vect as well
--but when should we do that???

vectConcat: (a: Type) -> (m:Nat) -> Vect m a -> (n:Nat) -> Vect n a -> (l:Nat) -> (pf: l = n+m) -> Vect l a  
--this is not enough, the list can still be anything, we should change that to Vect as well
--but when should we do that???


--in here, we need to refactor the usage of vectConcat
--many decisions needed here, relay to user?
--can use Refl here, but if we say nnn+1 then we can't

reverse31 :  (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) ->  (pf: m=k) -> Vect k a
reverse31 a m vec k pf = 
  case pf of Refl => vecElim  a 
                            (\n,v => Vect n a) 
                            ([])
                            (\nnn,x,xs,xsRes => vectConcat a nnn xsRes 1 (x::Nil) (1+nnn) Refl ) --(\nnn,x,xs,xsRes => vectConcat a nnn xsRes [x]  )
                                                    --vectDPConcat a 
                                                    --    xsRes 
                                                    --    [x] ) 
                            m
                            vec
                            
----refactor vectDPConcat so that it takes xsRes: Vect

vectConcat0: (a: Type) -> (dp1: DepPair Nat (\n => Vect n a)) -> List a -> DepPair Nat (\n => Vect n a) 
vectConcat0 a dp1 list2 = vecElim a 
                                    (\n,v=> DepPair Nat (\n => Vect n a) ) 
                                    (listToVect a list2)
                                    (\n,x,xs,xsRes => MkDepPair Nat (\m => Vect m a) 
                                                                (S (getDependee xsRes)) 
                                                                (x::(getDependant xsRes))) 
                                    (getDependee dp1)
                                    (getDependant dp1)

vectConcat1: (a: Type) -> (m:Nat) -> Vect m a -> (n:Nat) -> Vect n a -> DepPair Nat (\n => Vect n a) 
vectConcat1 a m vec1 n vec2 = vecElim a 
                                    (\n,v=> DepPair Nat (\n => Vect n a) ) 
                                    (MkDepPair Nat (\m => Vect m a) n vec2)
                                    (\n,x,xs,xsRes => MkDepPair Nat (\m => Vect m a) 
                                                                (S (getDependee xsRes)) 
                                                                (x::(getDependant xsRes))) 
                                    m
                                    vec1


vectConcat2: (a: Type) -> (m:Nat) -> Vect m a -> (n:Nat) -> Vect n a -> (l:Nat) -> (pf: l = n+m) -> Vect l a 
vectConcat2 a m vec1 n vec2 l pf = vecElim a 
                                    (\m,v=> Vect (n+m) a ) 
                                    (rewrite (plusZeroRightNeutral n) in vec2)
                                    (\m,x,xs,xsRes => rewrite ?tt in x::xRes)--MkDepPair Nat (\m => Vect m a) 
                                                      --          (S (getDependee xsRes)) 
                                                       --         (x::(getDependant xsRes))) 
                                    m
                                    vec1

--vectConcat: (a: Type) -> (m:Nat) -> Vect m a -> (n:Nat) -> Vect n a -> (l:Nat) -> (pf: l = n+m) -> Vect l a  


