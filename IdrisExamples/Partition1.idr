--partition example with list and vec eliminators

import Data.Nat
import Decidable.Equality
      
data MyList : Type -> Type where
     NilList : MyList a
     ConstructList : a -> MyList a -> MyList a


listElim:  (listEltType: Type) -> 
            (returnType: Type) -> 
            (nilcase: returnType) -> 
            (recursiveCombinator: (head: listEltType) -> (tail: MyList listEltType ) -> (recursionRes: returnType) -> returnType) -> 
            (MyList listEltType) -> 
            returnType
listElim listEltType returnType nilcase recursiveCombinator list = case list of 
                                                                        NilList => nilcase  
                                                                        ConstructList x xs => recursiveCombinator x xs ((listElim listEltType returnType nilcase recursiveCombinator) xs )

---------------------------------------------------

data MyVect : Nat -> Type -> Type where
     NilVect : MyVect Z a
     ConstructVect : a -> (k:Nat) -> MyVect k a -> MyVect (S k) a


VectElim:  (vecType: Type) -> 
            (returnTypeCalculator: (Nat -> Type) )-> 
            (nilcase: (returnTypeCalculator Z) ) -> 
            (recursiveCombinator: (vectHead: vecType) -> (tailLen: Nat) -> (tail: MyVect tailLen vecType )  -> (recursionRes: (returnTypeCalculator tailLen)) -> (returnTypeCalculator (S tailLen) ) ) ->  
            (inputVecLength: Nat) ->
            (inputVec: MyVect inputVecLength vecType) -> 
            (returnTypeCalculator inputVecLength)
VectElim vecType returnTypeCalculator  nilcase recursiveCombinator inputVecLength inputVec  
        = case inputVec of 
                    NilVect =>  nilcase
                    ConstructVect x k xs => recursiveCombinator x k xs (VectElim vecType returnTypeCalculator nilcase recursiveCombinator k xs ) 

                                  
-------------------------------------------------------------------------------

partition0 : (a: Type) -> (f : a -> Bool) -> (list : MyList a) -> (MyList a, MyList a)
partition0 a f list  = listElim a 
                                (MyList a, MyList a)
                                (NilList, NilList)
                                (recursiveCombinator)
                                list 
                        where recursiveCombinator : a -> MyList a -> (MyList a, MyList a) -> (MyList a, MyList a)    
                              recursiveCombinator x xs (lefts, rights)  = if f x then 
                                                                          ((ConstructList x lefts), rights)
                                                                        else 
                                                                          (lefts, (ConstructList x rights)) 


--partition0 Nat (\n=> lte n 3) (ConstructList 10 (ConstructList 2 (ConstructList 3  (ConstructList 4 NilList ) )) ) 

partition1 :  (a: Type) -> (f : a -> Bool) -> (m: Nat) -> (xs : MyVect m a) -> (MyList a, MyList a)
partition1 a f m vec  = VectElim a 
                                (\n => (MyList a, MyList a))
                                (NilList, NilList)
                                (recursiveCombinator)
                                m
                                vec 
                        where recursiveCombinator : a -> (n:Nat) -> ( MyVect n a) -> (MyList a, MyList a) -> (MyList a, MyList a)    
                              recursiveCombinator x  n xs (lefts, rights)  = if f x then 
                                                                            ((ConstructList x lefts), rights)
                                                                          else 
                                                                            (lefts, (ConstructList x rights)) 
             
--partition1 Nat (\n=> lte n 3) 4 (ConstructVect 10 3 (ConstructVect 2 2 (ConstructVect 3  1 (ConstructVect 4 0 NilVect ) )) ) 


partition2 :  (a: Type) -> (f : a -> Bool) -> (m: Nat) -> (xs : MyVect m a) -> ((k ** MyVect k a), (l ** MyVect l a)) 
partition2 a f m vec = VectElim a 
                                (\n => ((k ** MyVect k a), (l ** MyVect l a)) ) 
                                ((Z ** NilVect), (Z ** NilVect))
                                (recursiveCombinator)
                                m vec 
                         where recursiveCombinator : a -> (n:Nat) -> ( MyVect n a) ->  ((k ** MyVect k a), (l ** MyVect l a)) -> ((k ** MyVect k a), (l ** MyVect l a))  
                               recursiveCombinator x n xs ((k ** lefts), (l ** rights))  = if f x then 
                                                                                          (( (S k) ** (ConstructVect x k lefts)), (l ** rights))
                                                                                        else 
                                                                                          ( (k ** lefts), ( (S l) ** (ConstructVect x l rights))) 


--partition2 Nat (\n=> lte n 3) 4 (ConstructVect 10 3 (ConstructVect 2 2 (ConstructVect 3  1 (ConstructVect 4 0 NilVect ) )) ) 
