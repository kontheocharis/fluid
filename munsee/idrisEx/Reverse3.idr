--reverse without pattern matching

import Data.Nat

data MyList : Type -> Type where
     NilList : MyList a
     ConstructList : a -> MyList a -> MyList a



listElim:   (listEltType: Type) -> 
            (returnTypeCalc: (MyList listEltType -> Type)) -> 
            (nilcase: (returnTypeCalc NilList)  ) -> 
            (recursiveCombinator:   (head: listEltType) -> 
                                    (tailList: (MyList listEltType) ) ->
                                    (recursionRes: (returnTypeCalc tailList )) -> 
                                    returnTypeCalc (ConstructList head tailList) ) -> 
            (list: MyList listEltType) -> 
            (returnTypeCalc list)
listElim listEltType returnTypeCalc nilcase recursiveCombinator list = case list of 
                                                                        NilList => nilcase  
                                                                        ConstructList x xs => recursiveCombinator x xs ((listElim listEltType returnTypeCalc nilcase recursiveCombinator) xs )





myListConcat: (a: Type) -> MyList a -> MyList a -> MyList a 
myListConcat a list1 list2 = listElim a 
                                      (\x=> MyList a) 
                                      list2 
                                      (\x,xs, xsRes => ConstructList x xsRes ) 
                                      list1


-- myListConcat Nat NilList (ConstructList 1 (ConstructList 2 (ConstructList 3 NilList )) )
-- myListConcat Nat (ConstructList 1 (ConstructList 2 (ConstructList 3 NilList )) ) NilList 
-- myListConcat Nat (ConstructList 1 (ConstructList 2 (ConstructList 3 NilList )) ) (ConstructList 1 (ConstructList 2 (ConstructList 3 NilList )) )

-------------------------------------------------------------------------------

reverse0 :  (a: Type) ->  MyList a -> MyList a
reverse0 a l = listElim a 
                        (\x=> MyList a) 
                        (NilList) 
                        (\x,xs, xsRes => myListConcat a xsRes (ConstructList x NilList)  ) 
                        l

-- reverse0 Nat NilList 
-- reverse0 Nat (ConstructList 1 (ConstructList 2 (ConstructList 3  (ConstructList 4 NilList) )) )

-------------------------------------------------------------------------------
-- change input type



data MyVect : Nat -> Type -> Type where
     NilVect : MyVect Z a
     ConstructVect : a -> MyVect k a -> MyVect (S k) a



MyVectElim: (vecType: Type) -> 
            (returnTypeCalc: ((vectLen: Nat) -> 
                              (MyVect vectLen vecType) -> 
                              Type) )-> 
            (nilcase: (returnTypeCalc Z NilVect) ) -> 
            (recursiveCombinator: (vectHead: vecType) -> 
                                  (tailLen: Nat) -> 
                                  (tailVect: MyVect tailLen vecType) -> 
                                  (recursionRes: (returnTypeCalc tailLen tailVect)) -> 
                                  (returnTypeCalc (S tailLen) (ConstructVect vectHead tailVect) ) ) ->  
            (inputVecLength: Nat) ->
            (inputVec: MyVect inputVecLength vecType) -> 
            (returnTypeCalc inputVecLength inputVec)
MyVectElim vecType returnTypeCalc  nilcase recursiveCombinator inputVecLength inputVec = 
    case inputVec of 
        NilVect =>  nilcase
        ConstructVect x xs => recursiveCombinator x _ xs 
                                                  (MyVectElim vecType 
                                                              returnTypeCalc 
                                                              nilcase 
                                                              recursiveCombinator 
                                                              _ xs ) 


myVectConcat: (a: Type) -> (len1:Nat) -> (len2:Nat) -> 
               MyVect len1 a -> 
               MyVect len2 a ->  
               MyVect (len1 + len2) a 
myVectConcat a len1 len2 vec1 vec2 = 
    MyVectElim a 
               (\m,v => (MyVect len2 a -> MyVect (m + len2) a ))  
               (\v2 => v2)
               (\x, tailLen, xs, combineWithV2 => (\v2 => ConstructVect x (combineWithV2 v2)) )
               len1
               vec1
               vec2


-- myVectConcat Nat 0 3 NilVect (ConstructVect 1 (ConstructVect 2 (ConstructVect 3 NilVect )) )
-- myVectConcat Nat 3 0 (ConstructVect 1 (ConstructVect 2 (ConstructVect 3 NilVect )) ) NilVect
-- myVectConcat Nat 3 3 (ConstructVect 1 (ConstructVect 2 (ConstructVect 3 NilVect )) ) (ConstructVect 1 (ConstructVect 2 (ConstructVect 3 NilVect )) )


reverse1 :  (a: Type) -> (m:Nat) -> MyVect m a -> MyList a
reverse1 a m vec = 
    MyVectElim  a 
                (\n,v => MyList a) 
                (NilList)
                (\x,n,xs,xsRes => myListConcat a 
                                                xsRes 
                                                (ConstructList x NilList) ) 
                m vec

-- reverse1 Nat Z NilVect
-- reverse1 Nat 4 (ConstructVect 1 (ConstructVect 2 (ConstructVect 3 (ConstructVect 4 NilVect) )) )

reverse2 :  (a: Type) -> (m:Nat) -> MyVect m a -> (k : Nat ** MyVect k a) 
reverse2 a m vec = 
    MyVectElim  a 
                (\n,v => (k : Nat **  MyVect k a)) 
                (Z ** NilVect) 
                (\x,n,xs,(l**rres) => ( (l+1) ** ( myVectConcat a l (S Z) 
                                                                rres 
                                                                (ConstructVect x NilVect ) ) ) ) 
                m vec


-- reverse2 Nat Z NilVect
-- reverse2 Nat 4 (ConstructVect 1 (ConstructVect 2 (ConstructVect 3 (ConstructVect 4 NilVect) )) )


reverse3 : (a: Type) -> (m:Nat) -> MyVect m a -> (k:Nat) -> (pf: k=m) -> (MyVect k a) 
reverse3 a m vec k pf = 
    MyVectElim  a 
                (\n,v => MyVect n a) 
                (NilVect) 
                (\x,n,xs,rres => (rewrite (plusCommutative 1 n)  in
                                        (myVectConcat a n (S Z) 
                                                      rres 
                                                      (ConstructVect x NilVect ) ) ) ) 
                k 
                (rewrite pf in vec)

--TODO: use eqlim to the type I want

-- reverse3 Nat Z NilVect Z Refl
-- reverse3 Nat 4 (ConstructVect 1 (ConstructVect 2 (ConstructVect 3  (ConstructVect 4 NilVect) )) ) 4 Refl
