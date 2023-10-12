--reverse without pattern matching

import Data.Nat

data MyList : Type -> Type where
     NilList : MyList a
     ConstructList : a -> MyList a -> MyList a

listElim: (a: Type) -> 
          (MyList a)-> 
          (returnType: Type) -> --function
          (nilcase: MyList a -> returnType) -> --empty 
          (recursiveCase: a -> MyList a -> returnType) -> 
          returnType
listElim a l returnType nilcase recursiveCase = case l of 
                                                        NilList => nilcase l 
                                                        ConstructList x xs=> recursiveCase x xs  



listElim2:  (listEltType: Type) -> 
            (returnType: Type) -> 
            (nilcase: returnType) -> 
            (recursiveCombinator: (head: listEltType) -> (recursionRes: returnType) -> returnType) -> 
            (MyList listEltType) -> 
            returnType
listElim2 listEltType returnType nilcase recursiveCombinator list = case list of 
                                                                        NilList => nilcase  
                                                                        ConstructList x xs => recursiveCombinator x  ((listElim2 listEltType returnType nilcase recursiveCombinator) xs )



{-
--without elim
myListConcat: (a: Type) -> MyList a -> MyList a -> MyList a 
myListConcat a list1 list2 = case list1 of 
                                NilList => list2
                                ConstructList x xs=> ConstructList x (myListConcat a xs list2 )
-}

{-
--with elim
myListConcat: (a: Type) -> MyList a -> MyList a -> MyList a 
myListConcat a list1 list2 = listElim a list1 (MyList a) (\l => list2) (\x,xs => ConstructList x (myListConcat a xs list2 ) )
-}

myListConcat: (a: Type) -> MyList a -> MyList a -> MyList a 
myListConcat a list1 list2 = listElim2 a (MyList a) (list2) (\x,xsRes => ConstructList x xsRes ) list1


-- myListConcat Nat NilList (ConstructList 1 (ConstructList 2 (ConstructList 3 NilList )) )
-- myListConcat Nat (ConstructList 1 (ConstructList 2 (ConstructList 3 NilList )) ) NilList 
-- myListConcat Nat (ConstructList 1 (ConstructList 2 (ConstructList 3 NilList )) ) (ConstructList 1 (ConstructList 2 (ConstructList 3 NilList )) )


{- 
--pattern matching:
reverse0 :  (a: Type) ->  MyList a -> MyList a
reverse0 [] = []
reverse0 (x :: xs) = (reverse0 xs) ++ [x]
-}

{-
--case :
reverse0 :  (a: Type) ->  MyList a -> MyList a
reverse0 a l = case l of 
                NilList => NilList
                ConstructList x xs=> myListConcat a (reverse0 a xs) (ConstructList x NilList)
-}

{-
-- eliminator: 
reverse0 :  (a: Type) ->  MyList a -> MyList a
reverse0 a l = listElim a l (MyList a) (\list => list) (\x, xs => myListConcat a (reverse0 a xs) (ConstructList x NilList)   )
-}

-- eliminator: 
reverse0 :  (a: Type) ->  MyList a -> MyList a
reverse0 a l = listElim2 a (MyList a) (NilList) (\x, xsRes => myListConcat a xsRes (ConstructList x NilList)   ) l

-- reverse0 Nat NilList 
-- reverse0 Nat (ConstructList 1 (ConstructList 2 (ConstructList 3  (ConstructList 4 NilList) )) )

-------------------------------------------------------------------------------
-- change input type


data MyVect : Nat -> Type -> Type where
     NilVect : MyVect Z a
     ConstructVect : a -> (k:Nat) -> MyVect k a -> MyVect (S k) a

VectElim1: (m: Nat) -> (a: Type) -> (MyVect m a)-> (returnType: Type) -> 
            (nilcase: MyVect Z a -> returnType) -> (recursiveCase: a -> (n:Nat) -> MyVect n a -> returnType) -> returnType
VectElim1 m a v returnType nilcase recursiveCase = case v of 
                                                    NilVect => nilcase v 
                                                    ConstructVect x k xs => recursiveCase x k xs


VectElim2:  (vecType: Type) -> 
            (returnType: Type) -> 
            (nilcase: returnType) -> 
            (recursiveCombinator: vecType -> (tailLen: Nat) -> (recursionRes: returnType) -> returnType) -> 
            (MyVect m vecType) -> 
            returnType
VectElim2 vecType returnType nilcase recursiveCombinator v = case v of 
                                                            NilVect => nilcase  
                                                            ConstructVect x k xs => recursiveCombinator x k  ((VectElim2 vecType returnType nilcase recursiveCombinator) xs )


-- don't actually need this
VecToList: (m: Nat) -> (a: Type) -> (MyVect m a) -> MyList a
VecToList m a v = VectElim1 m a v (MyList a) (\x => NilList) (\x,n,xs => ConstructList x (VecToList n a xs))


VecToList2: (m: Nat) -> (a: Type) -> (MyVect m a) -> MyList a
VecToList2 m a v = VectElim2 a (MyList a) (NilList) (\x,n,res => (ConstructList x res) ) v

--VecToList2 4 Nat (ConstructVect 1 3 (ConstructVect 2 2 (ConstructVect 3  1 (ConstructVect 4 Z NilVect) )) )


{-
reverse1 : (m:Nat) -> MyVect m a -> MyList a
reverse1 Z [] = []
reverse1 (S m') (x :: xs) = let ys = reverse1 m' xs 
                                in ys ++ [x]
-}

{-
reverse1 : (m:Nat) -> (a: Type) -> MyVect m a -> MyList a
reverse1 m a vec = VectElim1 m a vec (MyList a) (\v => NilList) (\x,n,xs => myListConcat a (reverse1 n a xs) (ConstructList x NilList) )
-}

--reverse1 : (m:Nat) -> (a: Type) -> MyVect m a -> MyList a
--reverse1 m a vec = VectElim2 a (MyList a) (NilList) (\x,n,xsRes => myListConcat a xsRes (ConstructList x NilList) ) vec

-- reverse1 Z Nat NilVect
-- reverse1 4 Nat (ConstructVect 1 3 (ConstructVect 2 2 (ConstructVect 3  1 (ConstructVect 4 Z NilVect) )) )

-------------------------------------------------------------------------------
-- change output type

{-
reverse2 : (m:Nat) -> Vect m a -> (k : Nat ** Vect k a) 
reverse2 Z [] = (Z ** [])
reverse2 (S m') (x :: xs) = let (k' ** ys) = reverse2 m' xs in 
                                    ((k'+ 1)  ** (ys ++ [x]))
-}

{-
--recursionRes should not be of type returnType
VectElim3:  (vecType: Type) -> 
            (returnType: Type)-> 
            (nilcase: Nat -> returnType ) -> 
            (recursiveCombinator: (vectHead: vecType) -> (tailLen: Nat) -> (recursionRes: returnType) -> returnType) ->  
            (inputVecLength: Nat) ->
            (inputVec: MyVect inputVecLength vecType) -> 
            returnType
VectElim3 vecType returnType  nilcase recursiveCombinator inputVecLength inputVec 
    --= case inputVec of 
    --    NilVect =>  nilcase
    --    ConstructVect x k xs => recursiveCombinator x k  (VectElim3 vecType returnType nilcase recursiveCombinator k xs )
    = case inputVecLength of 
        Z =>  nilcase Z
        S k => case inputVec of 
                   -- NilVect =>  ?impos
                    ConstructVect x k xs => recursiveCombinator x k  (VectElim3 vecType returnType nilcase recursiveCombinator k xs ) 
-}    




--recursionRes should not be of type returnType!!!
VectElim:  (vecType: Type) -> 
            (returnTypeCalculator: (Nat -> Type) )-> 
            (nilcase: (returnTypeCalculator Z) ) -> 
            (recursiveCombinator: (vectHead: vecType) -> (tailLen: Nat) -> (recursionRes: (returnTypeCalculator tailLen)) -> (returnTypeCalculator (S tailLen) ) ) ->  
            (inputVecLength: Nat) ->
            (inputVec: MyVect inputVecLength vecType) -> 
            (returnTypeCalculator inputVecLength)
VectElim vecType returnTypeCalculator  nilcase recursiveCombinator inputVecLength inputVec  
        = case inputVec of 
                    NilVect =>  nilcase
                    ConstructVect x k xs => recursiveCombinator x k  (VectElim vecType returnTypeCalculator nilcase recursiveCombinator k xs ) 
{-    = case inputVecLength of 
        Z =>  nilcase 
        S k => case inputVec of 
                   -- NilVect =>  ?impos
                    ConstructVect x k xs => recursiveCombinator x k  (VectElim vecType returnTypeCalculator nilcase recursiveCombinator k xs ) 
-}

VecToList3: (m: Nat) -> (a: Type) -> (MyVect m a) -> MyList a
VecToList3 m a v = VectElim a (\n => MyList a) (NilList) (\x,n,res => (ConstructList x res) ) m v

--VecToList3 4 Nat (ConstructVect 1 3 (ConstructVect 2 2 (ConstructVect 3  1 (ConstructVect 4 Z NilVect) )) )


myVectConcat: (a: Type) -> (len1:Nat) -> (len2:Nat) -> MyVect len1 a -> MyVect len2 a ->  MyVect (len1 + len2) a 
myVectConcat a len1 len2 vec1 vec2 = VectElim 
                                        a 
                                        (\m => (MyVect len2 a -> MyVect (m + len2) a ))  
                                        (\v2 => v2)
                                        recursiveCombinator 
                                        len1
                                        vec1
                                        vec2
                                        where recursiveCombinator : (head: a) -> (tailLen : Nat) -> (MyVect len2 a -> MyVect (tailLen + len2) a) -> MyVect len2 a -> MyVect (S (plus tailLen len2)) a
                                              recursiveCombinator head tailLen combineWithV2 =  (\v2 => ConstructVect head (tailLen + len2) (combineWithV2 v2)) 


-- myVectConcat Nat 0 3 NilVect (ConstructVect 1 2 (ConstructVect 2 1 (ConstructVect 3 0 NilVect )) )
-- myVectConcat Nat 3 0 (ConstructVect 1 2 (ConstructVect 2 1 (ConstructVect 3 0 NilVect )) ) NilVect
-- myVectConcat Nat 3 3 (ConstructVect 1 2 (ConstructVect 2 1 (ConstructVect 3 0 NilVect )) ) (ConstructVect 1 2 (ConstructVect 2 1 (ConstructVect 3 0 NilVect )) )

{-
reverse2 : (m:Nat) -> Vect m a -> (k : Nat ** Vect k a) 
reverse2 Z [] = (Z ** [])
reverse2 (S m') (x :: xs) = let (k' ** ys) = reverse2 m' xs in 
                                    ((k'+ 1)  ** (ys ++ [x]))
-}



reverse1 : (m:Nat) -> (a: Type) -> MyVect m a -> MyList a
reverse1 m a vec = VectElim a (\n => MyList a) (NilList)
                     (\x,n,xsRes => myListConcat a xsRes (ConstructList x NilList) ) m vec

-- reverse1 Z Nat NilVect
-- reverse1 4 Nat (ConstructVect 1 3 (ConstructVect 2 2 (ConstructVect 3  1 (ConstructVect 4 Z NilVect) )) )



reverse2 : (m:Nat) -> (a: Type) -> MyVect m a -> (k : Nat ** MyVect k a) 
reverse2 m a vec = VectElim a 
                            (\n => (k : Nat **  MyVect k a) ) 
                            (Z ** NilVect) 
                            (recursiveCombinator) 
                            m vec
                            where recursiveCombinator: a -> Nat -> (k : Nat ** MyVect k a) -> (k : Nat ** MyVect k a)
                                  recursiveCombinator x n (l**xs) = ( (l+1) ** ( myVectConcat a l (S Z) xs (ConstructVect x Z NilVect ) ) )


-- reverse2 Z Nat NilVect
-- reverse2 4 Nat (ConstructVect 1 3 (ConstructVect 2 2 (ConstructVect 3  1 (ConstructVect 4 Z NilVect) )) )

-------------------------------------------------------------------------------
-- now require the proof of m=k

reverse3 : (m:Nat) -> (a: Type) -> MyVect m a -> (k:Nat) -> (pf: k=m) -> (MyVect k a) 
reverse3 m a vec k pf = VectElim a 
                                (\n => MyVect n a )   
                                (NilVect) 
                                (recursiveCombinator) 
                                k (rewrite pf in vec)
                                where recursiveCombinator:  a -> (tailLen : Nat) -> MyVect tailLen a -> MyVect (S tailLen) a
                                      recursiveCombinator x tailLen xs = 
                                                  rewrite  (plusCommutative 1 tailLen)  in     --use eqlim to the type I want
                                                                 ( myVectConcat a tailLen (S Z) xs (ConstructVect x Z NilVect ) ) 

-- reverse3 Z Nat NilVect Z Refl
-- reverse3 4 Nat (ConstructVect 1 3 (ConstructVect 2 2 (ConstructVect 3  1 (ConstructVect 4 Z NilVect) )) ) 4 Refl
