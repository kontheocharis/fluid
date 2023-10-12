--Rigner's method of refactoring

import Data.Nat
import Data.Vect

---------

len:  List a -> Nat 
len [] = Z 
len (x::xs) = S (len xs) 

listConcat: List a -> List a -> List a
listConcat [] list2 = list2
listConcat (x::xs) list2 = x::(listConcat xs list2)
-------------------------------------------------------------------------------
reverse0 :  List a -> List a
reverse0 [] = []
reverse0 (x :: xs) = listConcat (reverse0 xs) [x]

-- reverse0 [] 
-- reverse0 [1,2,3,4]

-------------------------------------------------------------------------------
--Step 1: work with list of length = m

--add index argumetn and constraint
--user claim that output len is equal to input length
reverseLenThm: (m:Nat) -> (list: List a) -> (constr: len list = m ) -> (len (reverse0 list) = m )
reverseLenThm Z [] contr = Refl
reverseLenThm (S n) (x::xs) contr = ?reverseLenThmh

--now we need to know the len of concatenation
--again, user input a theorem
concatLenThm: (m1:Nat) -> (list1: List a) -> (constr1: len list1 = m1 ) 
                -> (m2:Nat) -> (list2: List a) -> (constr2: len list2 = m2 ) 
                ->  (len (listConcat list1 list2) = (m1 + m2) )
concatLenThm Z [] Refl m2 list2 constr2 = constr2
concatLenThm (S n) (x::xs) constr1 m2 list2 constr2 = case constr1 of 
                                                            Refl => let hyp = (concatLenThm n xs Refl m2 list2 constr2) in 
                                                                        plusConstantLeft (len (listConcat xs list2)) (plus (len xs) m2) 1 hyp

-- combine thm with function
listConcatWithLen: (m1:Nat) -> (list1: List a) -> (constr1: len list1 = m1 ) -> 
                    (m2:Nat) -> (list2: List a) -> (constr2: len list2 = m2 ) ->  (l:List a **  len l = (m1 + m2) )
listConcatWithLen Z [] Refl m2 list2 constr2 = ( list2 ** constr2) 
listConcatWithLen (S n) (x::xs) constr1 m2 list2 constr2 = case constr1 of 
                                                            Refl => let recRes = listConcatWithLen n xs Refl m2 list2 constr2 in 
                                                                        let hyp = snd recRes in 
                                                                        let lenPf = plusConstantLeft (len (fst recRes)) (plus (len xs) m2) (1) (hyp)  in 
                                                                        (x::(fst recRes) ** lenPf)

--listConcatWithLen 2 [1,2] Refl 3 [4,5,6] Refl


--going back to reverseLenThm

reverseLenThm1: (m:Nat) -> (list: List a) -> (constr: len list = m ) -> (len (reverse0 list) = m )
reverseLenThm1 Z [] constr = Refl
reverseLenThm1 (S n) (x::xs) constr = case constr of 
                                                Refl => let hyp = (reverseLenThm1 n xs Refl) in 
                                                            let concatLenPf = (concatLenThm n (reverse0 xs) hyp 1 [x] Refl) in 
                                                                rewrite (plusCommutative 1 (len xs)) in concatLenPf

--now add the them back to reverse
--using dep pair here make sense? refinement types?

reverse1 :  (m:Nat) -> (list: List a) -> (constr: len list = m ) -> (l:List a ** len l = m )   
reverse1 m l constr =  (  (reverse0 l ) ** (reverseLenThm1 m l constr )) 
--reverse1 Z [] constr= ([] ** Refl)
--reverse1 (S n) (x :: xs) constr = case constr of Refl =>  ( (listConcat (reverse0 xs) [x]) ** (reverseLenThm1 (S n) (x::xs) Refl)) 

--need to remove references to reserse0
reverse12 :  (m:Nat) -> (list: List a) -> (constr: len list = m ) -> (l:List a ** len l = m ) 
reverse12 Z [] constr= ([] ** Refl)
reverse12  (S n) (x :: xs) constr = case constr of 
                                            Refl => let indLenPf = (snd (reverse12 n xs Refl)  ) in 
                                                      let concatwithSingle = listConcatWithLen n ( fst (reverse12 n xs Refl) ) indLenPf 1 [x] Refl in 
                                                            rewrite (plusCommutative 1 (len xs)) in concatwithSingle
                                                      

-- reverse12 Z [] Refl
-- reverse12 4 [1,2,3,4] Refl

-------------------------------------------------------------------------------
--change to vectdp
--also needs to change concat

vecConcatWithLen: (m1:Nat) ->  (vect1: (k:Nat ** Vect k a))  -> (constr1: fst vect1 = m1 ) 
                -> (m2:Nat) -> (vect2: (k:Nat ** Vect k a) )  -> (constr2: fst vect2 = m2 ) 
                ->  (w: (k:Nat ** Vect k a) ** (fst w = m1+m2)  )  
vecConcatWithLen Z (Z ** []) Refl m2 vect2 constr2 = (vect2 ** constr2 )
vecConcatWithLen m1 ((S n) ** (x::xs)) constr1 m2 vect2 constr2 = case constr1 of 
                                                            Refl => let recRes = vecConcatWithLen n (n ** xs) Refl m2 vect2 constr2 in 
                                                                        let hyp = snd recRes in 
                                                                        let lenPf = plusConstantLeft (fst (fst recRes)) (plus n m2) (1) (hyp)  in 
                                                                        ( ( S (fst (fst recRes)) ** x::(snd (fst recRes) )) ** lenPf) --need cons for vectdp

-- vecConcatWithLen 2 (2 ** [1,2]) Refl 3 (3**[4,5,6]) Refl

--now for reverse

reverse2 : (m:Nat) ->  (v: (l:Nat ** Vect l a)) -> (fst v = m ) -> (w: (k:Nat ** Vect k a) ** (fst w = m)  )  
reverse2 Z  (Z ** []) constr = ((Z ** []) ** Refl )
reverse2 m ((S n) ** (x::xs)) constr = case constr of 
                                            Refl => let indLenPf = (snd (reverse2 n (n ** xs) Refl)  ) in 
                                                        let concatwithSingle = vecConcatWithLen n (fst (reverse2 n (n ** xs) Refl)) indLenPf 1 (1 ** [x]) Refl in 
                                                             rewrite (plusCommutative 1 (n)) in concatwithSingle



-- reverse2 Z (Z ** []) Refl
-- reverse2 4 (4 ** [1,2,3,4]) Refl


-------------------------------------------------------------------------------
--change to vect

--first for concat
vecConcat: (m1:Nat) ->  (vect1: Vect m1 a)  
                -> (m2:Nat) ->  (vect2: Vect m2 a)  ->  Vect (m1+m2) a
vecConcat Z [] m2 vect2 = vect2
vecConcat (S n) (x::xs) m2 vect2  = x::(vecConcat n xs m2 vect2) 
                                                                       

--vecConcat 2 [1,2] 3 [4,5,6]

--then for reverse
reverse3 :  (m:Nat) ->  (v:  Vect m a) ->   Vect m a  
reverse3 Z [] = []
reverse3 (S n) (x::xs) = let concatwithSingle = vecConcat n (reverse3 n xs) 1 [x] in 
                            rewrite (plusCommutative 1 n) in concatwithSingle


-- reverse3 Z []
-- reverse3 4 [1,2,3,4]


-------------------------------------------------------------------------------
--assumed:
--algebraic ornaments
-- some prrof search (when proving length thms)