--partition example with list and vec eliminators

import Data.Nat
import Decidable.Equality
      
data MyList : Type -> Type where
     NilList : MyList a
     ConstructList : a -> MyList a -> MyList a


listElim:  (listEltType: Type) -> 
            (returnType: Type) -> 
            (nilcase: returnType) -> 
            (recursiveCombinator: (head: listEltType) -> (tail: (MyList listEltType)) ->(recursionRes: returnType) -> returnType) -> 
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
            (recursiveCombinator: (vectHead: vecType) -> (tailLen: Nat) -> (tail: MyVect tailLen vecType)-> (recursionRes: (returnTypeCalculator tailLen)) -> (returnTypeCalculator (S tailLen) ) ) ->  
            (inputVecLength: Nat) ->
            (inputVec: MyVect inputVecLength vecType) -> 
            (returnTypeCalculator inputVecLength)
VectElim vecType returnTypeCalculator  nilcase recursiveCombinator inputVecLength inputVec  
        = case inputVec of 
                    NilVect =>  nilcase
                    ConstructVect x k xs => recursiveCombinator x k xs (VectElim vecType returnTypeCalculator nilcase recursiveCombinator k xs ) 
     
                                  
-------------------------------------------------------------------------------                                                                

VecToList: (a: Type) -> (m: Nat) -> (MyVect m a) -> MyList a
VecToList a m v = VectElim a (\n => MyList a) (NilList) (\x,n,tail,res => (ConstructList x res) ) m v

-------------------------------------------------------------------------------


span0 : (a: Type) -> (f: a -> Bool) -> MyList a -> (MyList a, MyList a)
span0 a f list = listElim a 
                          (MyList a, MyList a) 
                          (NilList, NilList)
                          recursiveCombinator
                          list 
                    where recursiveCombinator : a -> MyList a -> (MyList a, MyList a) -> (MyList a, MyList a)
                          recursiveCombinator x xs (ys,zs) =  if f x then
                                                                ((ConstructList x ys), zs)
                                                              else
                                                                (NilList,(ConstructList x xs) )

--span0 Nat (\n=> lte n 3) (ConstructList 1 (ConstructList 2 (ConstructList 3 (ConstructList 4  (ConstructList 5 NilList ) )) ) )


span1 : (a: Type) -> (f: a -> Bool) -> (m : Nat) -> MyVect m a  -> (MyList a, MyList a)
span1 a f m vec  = VectElim a 
                            (\n => (MyList a, MyList a)) 
                            (NilList, NilList)
                            recursiveCombinator
                            m
                            vec 
                        where recursiveCombinator : a -> (tailLen : Nat) -> MyVect tailLen a -> (MyList a, MyList a) -> (MyList a, MyList a)
                              recursiveCombinator x tailLen xs (ys,zs) = if f x then
                                                                            ((ConstructList x ys), zs)
                                                                          else
                                                                            (NilList, (ConstructList x (VecToList a tailLen xs) ))

--span1 Nat (\n=> lte n 3) 5 (ConstructVect 2 4 (ConstructVect 1 3 (ConstructVect 3 2 (ConstructVect 5 1 (ConstructVect 7 0 NilVect ) )) ) )



span2 : (a: Type) -> (f: a -> Bool) -> (m : Nat) -> MyVect m a  ->  ((k ** MyVect k a), (l ** MyVect l a) )
span2 a f m vec  = VectElim a 
                            (\n => ((k ** MyVect k a), (l ** MyVect l a)) ) 
                            ((Z ** NilVect), (Z ** NilVect))
                            recursiveCombinator
                            m
                            vec 
                        where recursiveCombinator : a -> (tailLen : Nat) -> MyVect tailLen a 
                                                    -> ((k : Nat ** MyVect k a), (l : Nat ** MyVect l a)) 
                                                    -> ((k : Nat ** MyVect k a),(l : Nat ** MyVect l a))
                              recursiveCombinator x tailLen xs ((k ** ys), (l ** zs)) = if f x then
                                                                                          (((S k) ** (ConstructVect x k ys)), (l ** zs))
                                                                                        else
                                                                                          ((Z ** NilVect), ( (S tailLen) ** (ConstructVect x tailLen xs )))

--span2 Nat (\n=> lte n 3) 5 (ConstructVect 2 4 (ConstructVect 1 3 (ConstructVect 3 2 (ConstructVect 5 1 (ConstructVect 7 0 NilVect ) )) ) )
