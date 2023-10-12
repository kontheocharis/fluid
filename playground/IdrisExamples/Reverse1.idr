--reverse exameple using list and vec eliminators

import Data.Nat

data MyList : Type -> Type where
     NilList : MyList a
     ConstructList : a -> MyList a -> MyList a


listElim:  (listEltType: Type) -> 
            (returnType: Type) -> 
            (nilcase: returnType) -> 
            (recursiveCombinator: (head: listEltType) -> (tail: MyList listEltType) -> (recursionRes: returnType) -> returnType) -> 
            (MyList listEltType) -> 
            returnType
listElim listEltType returnType nilcase recursiveCombinator list = case list of 
                                                                        NilList => nilcase  
                                                                        ConstructList x xs => recursiveCombinator x xs ((listElim listEltType returnType nilcase recursiveCombinator) xs )


myListConcat: (a: Type) -> MyList a -> MyList a -> MyList a 
myListConcat a list1 list2 = listElim a (MyList a) (list2) (\x,xs,xsRes => ConstructList x xsRes ) list1

---------------------------------------------------

data MyVect : Nat -> Type -> Type where
     NilVect : MyVect Z a
     ConstructVect : a -> (k:Nat) -> MyVect k a -> MyVect (S k) a


VectElim:  (vecType: Type) -> 
            (returnTypeCalculator: (Nat -> Type) )-> 
            (nilcase: (returnTypeCalculator Z) ) -> 
            (recursiveCombinator: (vectHead: vecType) -> (tailLen: Nat) -> (tail: MyVect tailLen vecType)-> (recursionRes: (returnTypeCalculator tailLen)) -> (returnTypeCalculator (S tailLen) ) ) ->  
            (inputVecLength: Nat) ->
            (inputVec: MyVect inputVecLength vecType) -> 
            (returnTypeCalculator inputVecLength)
VectElim vecType returnTypeCalculator  nilcase recursiveCombinator inputVecLength inputVec  
        = case inputVec of 
                    NilVect =>  nilcase
                    ConstructVect x k xs => recursiveCombinator x k xs (VectElim vecType returnTypeCalculator nilcase recursiveCombinator k xs ) 


myVectConcat: (a: Type) -> (len1:Nat) -> (len2:Nat) -> MyVect len1 a -> MyVect len2 a ->  MyVect (len1 + len2) a 
myVectConcat a len1 len2 vec1 vec2 = VectElim 
                                        a 
                                        (\m => (MyVect len2 a -> MyVect (m + len2) a ))  
                                        (\v2 => v2)
                                        recursiveCombinator 
                                        len1
                                        vec1
                                        vec2
                                        where recursiveCombinator : (head: a) -> (tailLen : Nat) -> (MyVect tailLen a) -> (MyVect len2 a -> MyVect (tailLen + len2) a) -> MyVect len2 a -> MyVect (S (plus tailLen len2)) a
                                              recursiveCombinator head tailLen tail combineWithV2 =  (\v2 => ConstructVect head (tailLen + len2) (combineWithV2 v2)) 


---------------------------------------------------

reverse0 :  (a: Type) ->  MyList a -> MyList a
reverse0 a l = listElim a (MyList a) (NilList) (\x, xs, xsRes => myListConcat a xsRes (ConstructList x NilList)   ) l

-- reverse0 Nat NilList 
-- reverse0 Nat (ConstructList 1 (ConstructList 2 (ConstructList 3  (ConstructList 4 NilList) )) )

reverse1 : (m:Nat) -> (a: Type) -> MyVect m a -> MyList a
reverse1 m a vec = VectElim a (\n => MyList a) (NilList) (\x,n,xs,xsRes => myListConcat a xsRes (ConstructList x NilList) ) m vec

-- reverse1 Z Nat NilVect
-- reverse1 4 Nat (ConstructVect 1 3 (ConstructVect 2 2 (ConstructVect 3  1 (ConstructVect 4 Z NilVect) )) )

reverse2 : (m:Nat) -> (a: Type) -> MyVect m a -> (k : Nat ** MyVect k a) 
reverse2 m a vec = VectElim a 
                            (\n => (k : Nat **  MyVect k a) ) 
                            (Z ** NilVect) 
                            (recursiveCombinator) 
                            m vec
                            where recursiveCombinator: a -> (tailLen : Nat) -> (MyVect tailLen a) -> (k : Nat ** MyVect k a) -> (k : Nat ** MyVect k a)
                                  recursiveCombinator x n tail (l**xs) = ( (l+1) ** ( myVectConcat a l (S Z) xs (ConstructVect x Z NilVect ) ) )

-- reverse2 Z Nat NilVect
-- reverse2 4 Nat (ConstructVect 1 3 (ConstructVect 2 2 (ConstructVect 3  1 (ConstructVect 4 Z NilVect) )) )


reverse3 : (m:Nat) -> (a: Type) -> MyVect m a -> (k:Nat) -> (pf: k=m) -> (MyVect k a) 
reverse3 m a vec k pf = VectElim a 
                                (\n => MyVect n a )   
                                (NilVect) 
                                (recursiveCombinator) 
                                k (rewrite pf in vec)
                                where recursiveCombinator:  a -> (tailLen : Nat) -> (MyVect tailLen a) -> MyVect tailLen a -> MyVect (S tailLen) a
                                      recursiveCombinator x tailLen tail xs = rewrite  (plusCommutative 1 tailLen)  in  ( myVectConcat a tailLen (S Z) xs (ConstructVect x Z NilVect ) ) 

-- reverse3 Z Nat NilVect Z Refl
-- reverse3 4 Nat (ConstructVect 1 3 (ConstructVect 2 2 (ConstructVect 3  1 (ConstructVect 4 Z NilVect) )) ) 4 Refl
