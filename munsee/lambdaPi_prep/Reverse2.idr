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
--1 change list params to vec params

--1.1 add new Nat param (between param 2 and 3, but it does not matter).
--change in declaration and LHS of body only.   
reverse11 :  (a: Type) -> (m:Nat) -> List a -> List a
reverse11 a m l = listElim a 
                        (\x=> List a) 
                        ([] ) 
                        (\x,xs, xsRes => listConcat a xsRes [x]  ) 
                        l
---
--1.2 change type of param 1 to Vect m a
--change from listElim to VecElim 
--vecElim needs an extra param at position 1. This must be the newly added param 2 of function -> get from LHS
--param5 of vecElim can remain as the param4 of listElim
--param4 of vecElim can be param3 of listElim, but now needs to take another param. 
                -- Because the return type has not been change, the rest of the func can remain
--param3 of vecElim is param2 of listElim. again as return type is not changed, it can remain as it is
--param2 of vecElim is param1 of listElim, again with an extra Nat param.
   --eventhough xs is changed from list to vect, it is not used in the rhs so it remains            
--param1 of vecElim is the new param of the function
--param0 of vecElim is param0 of listElim              
reverse12 :  (a: Type) -> (m:Nat) -> Vect m a -> List a
reverse12 a m v = vecElim a 
                          (\n,x=> List a) 
                          ([] ) 
                          (\n,x,xs, xsRes => listConcat a xsRes [x]  ) 
                          m
                          v

---
--some name changes 
--(name change from l to vec)

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

-- reverse1 Nat Z []
-- reverse1 Nat 4 [1,2,3,4]

-------------------------------------------------------------------------------

data DepPair: (ty1: Type) -> 
                (term2Calc: ty1 -> Type) ->  Type  where
     MkDepPair: (ty1: Type) -> 
                 (term2Calc: ty1 -> Type) ->  
                (term1 : ty1)  -> 
                (term2: (term2Calc term1)) ->
                 DepPair ty1 term2Calc
     

getDependee: (DepPair ty1 term2Calc) -> ty1
getDependee pair = case pair of (MkDepPair ty1 term2Calc term1 term2) => term1 
--getDependee (MkDepPair Nat 3 (\n => Vect n Nat) [2,3,4])
--double check in lambda pi

getDependant: (pair: DepPair ty1 term2Calc) -> term2Calc (getDependee pair)
getDependant pair = case pair of (MkDepPair ty1 term2Calc term1 term2) => term2
--getDependant (MkDepPair Nat 3 (\n => Vect n Nat) [2,3,4])

-------------------------------------------------------------------------------
--2. Change output type to dependant pair 
{--generally when changing list to vec: 
  if list is param, directly change to vec 
     Q: we always do this? May need to change to depPair first and only change to Vec in certain safe condition 
  if list is return type, change to deppair
--}


--2.1. Change output type
-- List a becomes (DepPair Nat (\n => Vect n a) )
reverse21 :  (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )
reverse21 a m vec = ?rev21
{-    vecElim  a 
            (\n,v => List a) 
            ([])
            (\n,x,xs,xsRes => listConcat a 
                                         xsRes 
                                         [x] ) 
            m 
            vec
-}


--2.2. Change output type of eliminators
-- List a becomes (DepPair Nat (\n => Vect n a) )  
--!!!Q: how do we know that the List a in param4 is the output type of reverse22???? see example of listConcat
-- param0, param1 and param5 remains
reverse22 :  (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )
reverse22 a m vec = 
    vecElim  a 
             (\n,v => DepPair Nat (\n => Vect n a)) 
             ?rev22_baseCase --([])
             ?rev22_recCase
             --(\n,x,xs,xsRes => listConcat a 
             --                            xsRes 
             --                            [x] ) 
             m
             vec

--2.3.0 Fix base case of vecElim -- using listToVect
--l becomes (MkDepPair Nat (\n => Vect n a) (getDependee (listToVect a l)) (getDependant (listToVect a l)))
--alt: get correspondence from constructors of vec and list: NilList -> NilVect etc
--alt: get user to help, e.g. to change [] to (Z ** [])
listToVect : (a:Type) -> (xs : List a) -> (DepPair Nat (\m => Vect m a) )
listToVect a []  =  MkDepPair Nat (\m => Vect m a) Z []
listToVect a (x::xs) = MkDepPair Nat (\m => Vect m a) 
                                 (S (getDependee (listToVect a xs)) )  
                                 (x::(getDependant (listToVect a xs)))

reverse230 :  (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )
reverse230 a m vec = 
    vecElim  a 
             (\n,v => DepPair Nat (\n => Vect n a)) 
             (MkDepPair Nat (\n => Vect n a) (getDependee (listToVect a [])) (getDependant (listToVect a [])) )
             ?rev230_recCase
             --(\n,x,xs,xsRes => listConcat a 
             --                            xsRes 
             --                            [x] ) 
              m 
              vec       

-- 2 3.1 Partially evaluate terms
-- (getDependee (listToVect a [])) must be Z
-- (getDependant (listToVect a [])) must be NilVect 
reverse231 :  (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )
reverse231 a m vec = 
    vecElim  a 
             (\n,v => DepPair Nat (\n => Vect n a)) 
             (MkDepPair Nat (\n => Vect n a) Z [])
             ?rev231_recCase
             --(\n,x,xs,xsRes => listConcat a 
             --                            xsRes 
             --                            [x] ) 
              m 
              vec   


--2.4  Fix rec case of vecElim 
--input type has changed: now xsRes is nat**vec
--at the same time, output type has changed to nat**vec as well
--2.4.1: change output type: to decome pair, change input type name 

reverse241 :  (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )
reverse241 a m vec = 
    vecElim  a 
            (\n,v => DepPair Nat (\n => Vect n a)) 
             (MkDepPair Nat (\n => Vect n a) Z [])
             (\n,x,xs,depPair => (MkDepPair Nat (\n => Vect n a) 
                                            ?rev241_newn 
                                            ?rev241_concat))
             --                           listConcat a 
             --                            xsRes 
             --                            [x] ) 
              m 
              vec  

--TODO: use DP for eliminator --see refacprelude SigElim --see examples

-- n becomes  (getDependee depPair)    --!!!how can we know this!!!
-- xsRes becomes (getDependant depPair)
--needs to refactor the usage of listConcat
--listConcat a l1 l2 becomes vectConcat Nat (getDependee (listToVect a l1)) (getDependee (listToVect a l2)) (getDependant (listToVect a l1)) (getDependant (listToVect a l1))
-- but we no longer have lists l1 and l2, so we can't use listToVect

-----lift the recCase out and refactor -----
recCaseOri: (a:Type) -> (x: a) -> (xs:List a) -> (xsRes: List a) -> List a
recCaseOri a x xs xsRes = listConcat a 
                                     xsRes 
                                     [x] 

--add param n and change type from list to vect
--n and ns not used in body, nothing much to do here
recCaseOri1: (a:Type) -> (n : Nat)  -> (x: a) -> (xs:Vect n  a) -> (xsRes: List a) -> List a
recCaseOri1 a n x xs xsRes = listConcat a 
                                        xsRes 
                                        [x] 

--change type or param1 to DepPair Nat (\n => Vect n a) using ListToVect
-- now need to refactor listConcat
recCaseOri2: (a:Type) -> (n : Nat)  -> (x: a) -> (xs:Vect n  a) -> (xsRes: DepPair Nat (\n => Vect n a)) -> List a
recCaseOri2 a n x xs xsRes = ?rec2_listConcatOri --listConcat a 
                                        --xsRes 
                                        --[x] 

----refactor listConcat------List -> DepPair
listConcat1: (a: Type) -> List a -> List a -> List a 
listConcat1 a list1 list2 = listElim a 
                                    (\x=> List a) 
                                    list2 
                                    (\x,xs, xsRes => (x::xsRes) ) 
                                    list1

--change input type 1
--use elims for deppair and for vec
-- listElim -> vecElim with extra param (getDependee list1)
--list1 -> getDependee list1
listConcat2: (a: Type) -> (list1: DepPair Nat (\n => Vect n a)) -> List a -> List a 
listConcat2 a list1 list2 = vecElim a 
                                    (\n, x=> List a) 
                                    list2 
                                    (\n, x,xs, xsRes => (x::xsRes) ) 
                                    (getDependee list1)
                                    (getDependant list1)

--change input type 2
--list2 is the base case for vecElim
--need getDependant and vecToList? -the forgetful function in ornaments
vectDPToList : (a:Type) ->  (depPair: DepPair Nat (\m => Vect m a) ) -> (List a) 
vectDPToList a dp = vecElim a 
                            (\n,x => List a)
                            []
                            (\n, x,xs, xsRes => (x::xsRes) ) 
                            (getDependee dp)
                            (getDependant dp)

listConcat3: (a: Type) -> (list1: DepPair Nat (\n => Vect n a)) -> (list2:  DepPair Nat (\n => Vect n a))-> List a 
listConcat3 a list1 list2 = vecElim a 
                                    (\n, x=> List a) 
                                    (vectDPToList a list2) 
                                    (\n, x,xs, xsRes => (x::xsRes) ) 
                                    (getDependee list1)
                                    (getDependant list1)

--change output type 
--change output type of param5 of vecelim
--use listToVect on basecase
--for rec case, xsRes is now a dp, use listToVect and vectDPToList
listConcat4: (a: Type) -> (list1: DepPair Nat (\n => Vect n a)) -> (list2:  DepPair Nat (\n => Vect n a))-> DepPair Nat (\n => Vect n a) 
listConcat4 a list1 list2 = vecElim a 
                                    (\n, x=> DepPair Nat (\n => Vect n a)) 
                                    (listToVect a (vectDPToList a list2)) 
                                    (\n, x,xs, xsRes => listToVect a (x::(vectDPToList a xsRes)) ) 
                                    (getDependee list1)
                                    (getDependant list1)
--evaluate and simplify
-- (listToVect a (vectDPToList a d)) is just getDependant d -- need to know that they are (almost) inverse of each other
-- listToVect (listConstruct x xs) =  1+ getDependee(listToVect xs)  ** vecConstruct x (getDependent (listToVect xs))
listConcat5: (a: Type) -> (list1: DepPair Nat (\n => Vect n a)) -> (list2:  DepPair Nat (\n => Vect n a))-> DepPair Nat (\n => Vect n a) 
listConcat5 a list1 list2 = vecElim a 
                                    (\n, x=> DepPair Nat (\n => Vect n a)) 
                                    (list2) 
                                    (\n, x,xs, xsRes =>  MkDepPair Nat (\n => Vect n a) 
                                                                   (1+(getDependee (listToVect a (vectDPToList a xsRes)))) 
                                                                   (x::(getDependant (listToVect a (vectDPToList a xsRes)))) ) 
                                    (getDependee list1)
                                    (getDependant list1)
--again simplify
listConcat6: (a: Type) -> (list1: DepPair Nat (\n => Vect n a)) -> (list2:  DepPair Nat (\n => Vect n a))-> DepPair Nat (\n => Vect n a) 
listConcat6 a list1 list2 = vecElim a 
                                    (\n, x=> DepPair Nat (\n => Vect n a)) 
                                    (list2) 
                                    (\n, x,xs, xsRes =>  MkDepPair Nat (\n => Vect n a) 
                                                                   (1+(getDependee xsRes)) 
                                                                   (x::(getDependant xsRes)) ) 
                                    (getDependee list1)
                                    (getDependant list1)
--rename                                   
vectDPConcat: (a: Type) -> (dp1: DepPair Nat (\n => Vect n a)) -> (dp2:  DepPair Nat (\n => Vect n a))-> DepPair Nat (\n => Vect n a) 
vectDPConcat a dp1 dp2 = vecElim a 
                                    (\n, x=> DepPair Nat (\n => Vect n a)) 
                                    (dp2) 
                                    (\n, x,xs, xsRes =>  MkDepPair Nat (\n => Vect n a) 
                                                                   (1+(getDependee xsRes)) 
                                                                   (x::(getDependant xsRes)) ) 
                                    (getDependee dp1)
                                    (getDependant dp1)

--[END]--refactor listConcat------

{-recCaseOri2: (a:Type) -> (n : Nat)  -> (x: a) -> (xs:Vect n  a) -> (xsRes: DepPair Nat (\n => Vect n a)) -> List a
recCaseOri2 a n x xs xsRes = ?rec2_listConcatOri --listConcat a 
                                        --xsRes 
                                        --[x] 
-}
-- list -> listToVec list  
recCase3: (a:Type) -> (n : Nat)  -> (x: a) -> (xs:Vect n  a) -> (xsRes: DepPair Nat (\n => Vect n a)) -> DepPair Nat (\n => Vect n a)
recCase3 a n x xs xsRes = vectDPConcat  a 
                                       xsRes
                                       (listToVect a [x])


--[END]---lift the recCase out and refactor -----

reverse242_recCase: (a:Type) -> (n : Nat)  -> (x: a) -> (xs:Vect n  a) -> 
                    (xsRes: DepPair Nat (\n => Vect n a)) -> DepPair Nat (\n => Vect n a)
reverse242_recCase a n x xs xsRes = vectDPConcat  a 
                                                  xsRes
                                                  (listToVect a [x])


reverse242 :  (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )
reverse242 a m vec = 
    vecElim  a 
             (\n,v => DepPair Nat (\n => Vect n a)) 
             (MkDepPair Nat (\n => Vect n a) Z [])
             (reverse242_recCase a)
              m 
              vec  

--put reverse242_recCase back in
reverse243 :  (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )
reverse243 a m vec = 
    vecElim  a 
             (\n,v => DepPair Nat (\n => Vect n a)) 
             (MkDepPair Nat (\n => Vect n a) Z [])
             (\n, x, xs, xsRes => vectDPConcat  a 
                                                xsRes
                                                (listToVect a [x]))
              m 
              vec  

{-
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
-}
-------
reverse2 :  (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )
reverse2 a m vec = 
    vecElim  a 
             (\n,v => DepPair Nat (\n => Vect n a)) 
             (MkDepPair Nat (\n => Vect n a) Z [])
             (\n, x, xs, xsRes => vectDPConcat  a 
                                                xsRes
                                                (listToVect a [x]))
              m 
              vec  

-- reverse2 Nat Z []
-- reverse2 Nat 4 [1,2,3,4]

{- 
--previous attempt on reverse2
reverse2 :  (a: Type) -> (m:Nat) -> Vect m a -> (DepPair Nat (\n => Vect n a) )
reverse2 a m vec = 
        vecElim a 
                (\n,v => DepPair Nat (\n => Vect n a)) 
                (MkDepPair Nat (\n => Vect n a) Z [])
                (\n,x,xs,depPair  => (MkDepPair  Nat 
                                                (\n => Vect n a)
                                                ((getDependee depPair) +1) 
                                                (vectConcat a 
                                                            (getDependee depPair) 
                                                            (S Z) 
                                                            (getDependant depPair)
                                                            [x] )  ) ) 
                m vec
-}

-------------------------------------------------------------------------------
-- 3. requires proof that m=k

--3.1 add k and pf as param
reverse31 :  (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (DepPair Nat (\n => Vect n a) )
reverse31 a m vec k pf = 
    vecElim  a 
             (\n,v => DepPair Nat (\n => Vect n a)) 
             (MkDepPair Nat (\n => Vect n a) Z [])
              (\n, x, xs, xsRes => vectDPConcat  a 
                                                xsRes
                                                (listToVect a [x]))
              m 
              vec  

--3.2 change return type to Vect k a
-- what is the new return type of param4? 

--3.2.1 fix return type
reverse321 :  (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a)
reverse321 a m vec k pf = 
    vecElim  a 
             (\m,vec => ( (k:Nat) -> (pf: m=k) -> Vect k a)) 
             ?rev321_basecase
             --(MkDepPair Nat (\n => Vect n a) Z [])
             ?rev321_reccase
             --(\n, x, xs, xsRes => vectDPConcat  a 
             --                                   xsRes
             --                                   (listToVect a [x]))
              m 
              vec  
              k pf

--TODO: use eqElim !!! reut type shoudl just be Vect k a

--3.2.2 fix base case
-- use case Refl 
reverse322 :  (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a)
reverse322 a m vec k pf = 
    vecElim  a 
             (\m,vec => ( (k:Nat) -> (pf: m=k) -> Vect k a)) 
             (\k, pf => case pf of Refl => [] )          
             ?rev322_reccase
             --(\n, x, xs, xsRes => vectDPConcat  a 
             --                                   xsRes
             --                                   (listToVect a [x]))
              m 
              vec  
              k pf

--3.2.3 fix rec case
-- lift rec case 

----refactor reverse323 rec case -------

--3.2.3.1 
--Take original rev case 
rev3231ReccaseOri1: (a: Type) ->  (n : Nat) -> (x:a)  -> (xs: Vect n a)  -> (xsRes: (DepPair Nat (\n => Vect n a))) -> DepPair Nat (\n => Vect n a)
rev3231ReccaseOri1 a n x xs xsRes = vectDPConcat  a 
                                                 xsRes
                                                 (listToVect a [x])

--3.2.3.2 
--change input type
-- now need to refactor vectDPConcat

----refactor vectDPConcat -------
--add params a and n
vectDPConcatOri: (a: Type) -> (n : Nat) -> (dp1: DepPair Nat (\n => Vect n a)) -> (dp2:  DepPair Nat (\n => Vect n a))-> DepPair Nat (\n => Vect n a) 
vectDPConcatOri a n dp1 dp2 = vecElim a 
                                    (\n, x=> DepPair Nat (\n => Vect n a)) 
                                    (dp2) 
                                    (\n, x,xs, xsRes =>  MkDepPair Nat (\n => Vect n a) 
                                                                   (1+(getDependee xsRes)) 
                                                                   (x::(getDependant xsRes)) ) 
                                    (getDependee dp1)
                                    (getDependant dp1)


-- change input type 1 
-- should we refactor the second input??? how do we know to do that?? users should say
vectDPConcat2: (a: Type) -> (n : Nat) -> (dp1f: (k : Nat) -> n = k -> Vect k a) -> (dp2:  DepPair Nat (\n => Vect n a))-> DepPair Nat (\n => Vect n a) 
vectDPConcat2 a n dp1f dp2 = vecElim a 
                                    (\n, x=> DepPair Nat (\n => Vect n a)) 
                                    (dp2) 
                                    (\n, x,xs, xsRes =>  MkDepPair Nat (\n => Vect n a) 
                                                                   (1+(getDependee xsRes)) 
                                                                   (x::(getDependant xsRes)) ) 
                                    ?vectDPConcat2_num--(getDependee dp1)
                                    ?vectDPConcat2_vec--(getDependant dp1)

-- (k ** Vect k a) becomes  n and (dp1f n Refl)
--Q: hoe to know this? Because we need n=k so we put in n?
vectDPConcat3: (a: Type) -> (n : Nat) ->  (dp1f: (k : Nat) -> n = k -> Vect k a) -> (dp2:  DepPair Nat (\n => Vect n a))-> DepPair Nat (\n => Vect n a) 
vectDPConcat3 a n dp1f dp2 = vecElim a 
                                    (\n, x=> DepPair Nat (\n => Vect n a)) 
                                    (dp2) 
                                    (\n, x,xs, xsRes =>  MkDepPair Nat (\n => Vect n a) 
                                                                   (1+(getDependee xsRes)) 
                                                                   (x::(getDependant xsRes)) ) 
                                    n
                                    (dp1f n Refl)

--[END]-refactor vectDPConcat -------

rev3231vectDPConcat2: (a: Type) -> (n : Nat)  -> (dp1f: (k : Nat) -> n = k -> Vect k a)-> (dp2:  DepPair Nat (\n => Vect n a))-> DepPair Nat (\n => Vect n a) 
rev3231vectDPConcat2 a n dp1f dp2 = vecElim a 
                                        (\n, x=> DepPair Nat (\n => Vect n a)) 
                                        (dp2) 
                                        (\n, x,xs, xsRes =>  MkDepPair Nat (\n => Vect n a) 
                                                                        (1+(getDependee xsRes)) 
                                                                        (x::(getDependant xsRes)) ) 
                                        n
                                        (dp1f n Refl)


rev3231ReccaseOri2: (a: Type) ->  (n : Nat) -> (x:a)  -> (xs: Vect n a)  ->  (xsRes: (k : Nat) -> n = k -> Vect k a) -> DepPair Nat (\n => Vect n a)
rev3231ReccaseOri2 a n x xs xsRes = rev3231vectDPConcat2  a n
                                                          xsRes
                                                          (listToVect a [x]) 

--add input k and pf
rev3231ReccaseOri3: (a: Type) ->  (n : Nat) -> (x:a)  -> (xs: Vect n a)  ->  (xsRes: (k : Nat) -> n = k -> Vect k a) -> (k : Nat) -> (pf:S n = k) -> DepPair Nat (\n => Vect n a)
rev3231ReccaseOri3 a n x xs xsRes k pf = rev3231vectDPConcat2  a n
                                                          xsRes
                                                          (listToVect a [x]) 

--change output type
rev3231ReccaseOri4: (a: Type) ->  (n : Nat) -> (x:a)  -> (xs: Vect n a)  ->  (xsRes: (k : Nat) -> n = k -> Vect k a) -> (k : Nat) -> (pf:S n = k) -> Vect k a
rev3231ReccaseOri4 a n x xs xsRes k pf = ?rev3231Reccase_Ori4{-rev3231vectDPConcat2  a n
                                                          xsRes
                                                          (listToVect a [x]) -}

---- refactor rev3231vectDPConcat2 yet again 

--[END]-- refactor rev3231vectDPConcat2 yet again 

-- this is wrong -- only have (S n = k) = because we concat with a singleton!!!!!
rev3231vectDPConcatVect: (a: Type) -> (n : Nat)  -> 
(dp1f: (k : Nat) -> n = k -> Vect k a)-> 
(dp2:  DepPair Nat (\n => Vect n a)) -> (k : Nat) -> (pf:S n = k) -> Vect k a 
--TODO: copy final here

rev3231ReccaseOri5: (a: Type) ->  (n : Nat) -> (x:a)  -> (xs: Vect n a)  ->  (xsRes: (k : Nat) -> n = k -> Vect k a) -> (k : Nat) -> (pf:S n = k) -> Vect k a
rev3231ReccaseOri5 a n x xs xsRes k pf = rev3231vectDPConcatVect  a n
                                                          xsRes
                                                          (listToVect a [x]) 
                                                          k pf


--[END]--refactor reverse323 rec case -------

rev323Reccase: (a: Type) ->  (n : Nat) -> (x:a) -> (xs: Vect n a) -> 
                (xsRes: (k : Nat) -> n = k -> Vect k a) -> (k : Nat) -> (pf:S n = k) -> Vect k a
rev323Reccase a n x xs xsRes k pf = rev3231vectDPConcatVect  a n
                                                          xsRes
                                                          (listToVect a [x]) 
                                                          k pf
--TODO: copy final version here

reverse323 :  (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a)
reverse323 a m vec k pf = 
    vecElim  a 
             (\m,vec => ( (k:Nat) -> (pf: m=k) -> Vect k a)) 
             (\k, pf => case pf of Refl => [] )          
             (rev323Reccase a)
             --(\n, x, xs, xsRes => vectDPConcat  a 
             --                                   xsRes
             --                                   (listToVect a [x]))
              m 
              vec  
              k pf



----------------------------------------------------------------------------------
-- another attempt - works!!


--3.2.3 fix rec case
-- use Nat elim on k
-- Q: why don't we refactor vectDPConcat instead? Not yet, will do that next
reverse323a :  (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a)
reverse323a a m vec k pf = 
    vecElim  a 
             (\m,vec => ( (k:Nat) -> (pf: m=k) -> Vect k a)) 
             (\k, pf => case pf of Refl => [] )          
             (\m, x, xs, xsRes => (\k, pf =>  --pf: S m = k
                                       case k of 
                                            Z impossible -- S m = Z
                                            (S n) => ?rev323_Sn )   )      
            --                                    vectDPConcat  a 
             --                                   xsRes
             --                                   (listToVect a [x]))
              m 
              vec  
              k pf

--3.2.4 fix rec case
-- ??
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

{- 
case k = S n
we have S m = S n 
Then can get pf' : m = n
xsRes n pf' gives a Vect (n) a 
we concat that with [x] to get a vector of size (n+1)
rewrite to get vector of size (S n)
-}
--TODO use pSnIsNot0  and void elim


-- reverse324a Nat Z [] Z Refl
-- reverse324a Nat 4 [1,2,3,4] 4 Refl


{-
--prev attempt:
reverse3 : (a: Type) -> (m:Nat) -> Vect m a -> (k:Nat) -> (pf: m=k) -> (Vect k a) 
reverse3 a m vec k pf = 
        vecElim a 
                (\n,v => Vect n a)  --why n?
                ([]) 
                (\n,x,xs,rres => apply2  (Vect (Prelude.plus n 1) a) 
                                         (Vect (Prelude.plus 1 n) a) 
                                         (leibniz Nat Type 
                                                  (\n' => Vect n' a) 
                                                  (Prelude.plus n 1) 
                                                  (Prelude.plus 1 n) 
                                                  (plusCommutative n 1))
                                         (vectConcat a 
                                                     n 
                                                     (S Z) 
                                                     rres 
                                                     [x] ) ) 
                k 
                (apply2  (Vect m a) 
                         (Vect k a) 
                         (leibniz Nat 
                                  Type 
                                  (\n => Vect n a) 
                                  m k pf)
                          vec)
-}


-----look at append example!!! Index