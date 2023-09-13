--quicksort (not in-place) example
--adding correctness proof
--TODO: maybe: make life easier by doing list over Nat!


import Prelude.EqOrd
import Data.Vect

--------------------------------------------

--we start with the all in one version
quicksort0 :  (Ord a) => List a -> List a 
quicksort0 [] = []
quicksort0 (x::xs) = 
  quicksort0 (fst (smallerAndBigger0 xs)) 
  ++ (x::(quicksort0 (snd (smallerAndBigger0 xs))) )
    where smallerAndBigger0: List a -> (List a ,List a)
          smallerAndBigger0 [] = ([],[])
          smallerAndBigger0 (y::ys) = 
            let recRes = (smallerAndBigger0 ys) in 
              case  (y <= x)  of 
                False =>  (fst recRes,  y::(snd recRes) ) 
                True  => (y::(fst recRes),  snd recRes )
--quicksort0 [3,6,45,7,2,34,6]

--------------------------------------------

--try to make it tighter with SortedPf


data ListLEq10: a -> List a -> Type where 
  ListLEqIKB10: (x:a) -> (l: List a) -> ListLEq10 x l  
  --this is a IKnowBetter construct

data ListGT10: a -> List a -> Type where 
  ListGTIKB10: (x:a) -> (l: List a) -> ListGT10 x l  
  --this is a IKnowBetter construct

data SortedPf10 : List a -> Type where
  NilIsSorted10 : SortedPf10 [] 
  ConcatSorted10: (x:a) -> 
                (l1: List a) -> SortedPf10 l1 -> ListLEq10 x l1 -> 
                (l2: List a) -> SortedPf10 l2 -> ListGT10 x l2 ->  
                SortedPf10 (l1 ++ (x::l2))
                -- if l1 is a sorted list with elements leq x
                -- and l2 is a sprted list with elements greater than x 
                -- then l1 ++ (x::l2) is sorted 

--TODO: concat to cons - use View?

--change return type to (l: List a ** SortedPf10 l)
quicksort10 :  (Ord a) => List a -> (l: List a **  SortedPf10 l)
quicksort10 [] = ( [] ** NilIsSorted10 )
quicksort10 (x::xs) = 
  ( fst (quicksort10 (fst (smallerAndBigger0 xs))) 
    ++ (x::(fst (quicksort10 (snd (smallerAndBigger0 xs)))) )
   **
    ?pp_qsort10
  )
    where smallerAndBigger0: List a -> (List a ,List a)
          smallerAndBigger0 [] = ([],[])
          smallerAndBigger0 (y::ys) = 
            let recRes = (smallerAndBigger0 ys) in 
              case  (y <= x)  of 
                False => (fst recRes,  y::(snd recRes) ) 
                True  => (y::(fst recRes), snd recRes )


-- fill hole with ConcatSorted
quicksort11 :  (Ord a) => List a -> (l: List a **  SortedPf10 l)
quicksort11 [] = ( [] ** NilIsSorted10 )
quicksort11 (x::xs) = 
  let resSmall = (quicksort11 (fst (smallerAndBigger0 xs)))
      resBig = (quicksort11 (snd (smallerAndBigger0 xs)))
    in ( fst resSmall
          ++ (x::(fst resBig) )
        **
          (ConcatSorted10 x 
                          (fst resSmall)
                          (snd resSmall)
                          ?lessTpf_qsort11
                          (fst resBig)
                          (snd resBig)
                          ?moreTpf_qsort11
          )
        )
          where smallerAndBigger0: List a -> (List a ,List a)
                smallerAndBigger0 [] = ([],[])
                smallerAndBigger0 (y::ys) = 
                  let recResSB = (smallerAndBigger0 ys) in 
                    case  (y <= x)  of 
                      False => (fst recResSB,  y::(snd recResSB) ) 
                      True  => (y::(fst recResSB), snd recResSB )

--smallerAndBigger0 should give smaller and bigger pfs
quicksort12 :  (Ord a) => List a -> (l: List a **  SortedPf10 l)
quicksort12 [] = ( [] ** NilIsSorted10 )
quicksort12 (x::xs) = 
  let resSmall = (quicksort12 (fst (fst (smallerAndBigger0 xs))))
      resBig = (quicksort12 (fst (snd (smallerAndBigger0 xs))))
    in ( fst resSmall
          ++ (x::(fst resBig) )
        **
          (ConcatSorted10 x 
                          (fst resSmall)
                          (snd resSmall)
                          ?lessTpf_qsort13
                          (fst resBig)
                          (snd resBig)
                          ?moreTpf_qsort13
          )
        )
          where smallerAndBigger0: List a -> ((s: List a ** ListLEq10 x s) 
                                              , 
                                              (b: List a ** ListGT10 x b ))
                smallerAndBigger0 [] = (([] ** ListLEqIKB10 x [] ),
                                        ([] ** ListGTIKB10 x []))
                smallerAndBigger0 (y::ys) = 
                  let recResSB = (smallerAndBigger0 ys) in 
                    case  (y <= x)  of 
                      False => let newS = fst (fst recResSB) 
                                   newB = (y::(fst (snd recResSB))) 
                                  in ((newS ** ListLEqIKB10 x newS ),  
                                      (newB ** ListGTIKB10 x newB ) ) 
                      True  => let newS = (y::(fst (fst recResSB))) 
                                   newB = fst (snd recResSB)
                                  in ((newS ** ListLEqIKB10 x newS ),  
                                      (newB ** ListGTIKB10 x newB ) ) 
  
--when using IKBs, we are asserting something is true
--typechecker will not check it, so need to be extra careful


--now we try to complete holes in concatsorted 
--but we need that quicksort of a listLEQ is still ListLEQ
--add lemma as func
--sim for big lists

quicksort13 :  (Ord a) => List a -> (l: List a **  SortedPf10 l)
quicksort13 [] = ( [] ** NilIsSorted10 )
quicksort13 (x::xs) = 
  let sbres = (smallerAndBigger0 xs)
      --resSmall = (quicksort13 (fst (fst sbres)))
      --resBig = (quicksort13 (fst (snd sbres)))
    in ( fst (quicksort13 (fst (fst sbres)))
          ++ (x::(fst (quicksort13 (fst (snd sbres)))) )
        **
          (ConcatSorted10 x 
                          (fst (quicksort13 (fst (fst sbres))))
                          (snd (quicksort13 (fst (fst sbres))))
                          (qsortSmallIsStillSmall x ((fst (fst sbres)) ** (snd (fst sbres))))  
                          (fst (quicksort13 (fst (snd sbres))))
                          (snd (quicksort13 (fst (snd sbres))))
                          (qsortBigIsStillBig x ((fst (snd sbres)) ** (snd (snd sbres))))   
          )
        )
          where smallerAndBigger0: List a -> ((s: List a ** ListLEq10 x s) 
                                              , 
                                              (b: List a ** ListGT10 x b ))
                smallerAndBigger0 [] = (([] ** ListLEqIKB10 x [] ),
                                        ([] ** ListGTIKB10 x []))
                smallerAndBigger0 (y::ys) = 
                  let recResSB = (smallerAndBigger0 ys) in 
                    case  (y <= x)  of 
                      False => let newS = fst (fst recResSB) 
                                   newB = (y::(fst (snd recResSB))) 
                                  in ((newS ** ListLEqIKB10 x newS ),  
                                      (newB ** ListGTIKB10 x newB ) ) 
                      True  => let newS = (y::(fst (fst recResSB))) 
                                   newB = fst (snd recResSB)
                                  in ((newS ** ListLEqIKB10 x newS ),  
                                      (newB ** ListGTIKB10 x newB ) ) 
                qsortSmallIsStillSmall: (bound:a) -> (sl: List a ** ListLEq10 bound l) 
                                          -> ListLEq10 bound (fst (quicksort13 sl))
                qsortSmallIsStillSmall m dp = ?stillSpf_qsort13
                qsortBigIsStillBig: (bound:a) -> (sl: List a ** ListGT10 bound l) 
                                      -> ListGT10 bound (fst (quicksort13 sl))
                qsortBigIsStillBig m dp = ?stillBpf_qsort13

--quicksort13 [3,6,45,7,2,34,6]

--now how to prove qsortSmallIsStillSmall and qsortBigIsStillBig?
  -- qsprt of the concatenation of smaller head and bigger
  -- head is in list so is small by assumption
  -- elements of small and big are also taken from the list so again is small

-- how can we claim it's true here? 



--quicksort14 :  (Ord a) => p: List a -> (SortedPf10 p)

quicksort14 :  (Ord a) => List a -> (l: List a **  SortedPf10 l)
quicksort14 [] = ( [] ** NilIsSorted10 )
quicksort14 (x::xs) = 
  let sbres = (smallerAndBigger0 xs)
    in ( fst (quicksort14 (fst (fst sbres)))
          ++ (x::(fst (quicksort14 (fst (snd sbres)))) )
        **
          (ConcatSorted10 x 
                          (fst (quicksort14 (fst (fst sbres))))
                          (snd (quicksort14 (fst (fst sbres))))
                          (qsortSmallIsStillSmall x ((fst (fst sbres)) ** (snd (fst sbres))))  
                          (fst (quicksort14 (fst (snd sbres))))
                          (snd (quicksort14 (fst (snd sbres))))
                          (qsortBigIsStillBig x ((fst (snd sbres)) ** (snd (snd sbres))))   )
        ) where smallerAndBigger0: List a -> ((s: List a ** ListLEq10 x s) 
                                              , 
                                              (b: List a ** ListGT10 x b ))
                smallerAndBigger0 [] = (([] ** ListLEqIKB10 x [] ),
                                        ([] ** ListGTIKB10 x []))
                smallerAndBigger0 (y::ys) = 
                  let recResSB = (smallerAndBigger0 ys) in 
                    case  (y <= x)  of 
                      False => let newS = fst (fst recResSB) 
                                   newB = (y::(fst (snd recResSB))) 
                                  in ((newS ** ListLEqIKB10 x newS ),  
                                      (newB ** ListGTIKB10 x newB ) ) 
                      True  => let newS = (y::(fst (fst recResSB))) 
                                   newB = fst (snd recResSB)
                                  in ((newS ** ListLEqIKB10 x newS ),  
                                      (newB ** ListGTIKB10 x newB ) ) 
                qsortSmallIsStillSmall: (bound:a) -> (dp:(sl: List a ** ListLEq10 bound sl)) 
                                          -> ListLEq10 bound (fst (quicksort14 (fst dp)))
                qsortSmallIsStillSmall m dp = ListLEqIKB10 m  (fst (quicksort14 (fst dp)))
                qsortBigIsStillBig: (bound:a) -> (dp:(sl: List a ** ListGT10 bound sl)) 
                                      -> ListGT10 bound (fst (quicksort14 (fst dp)))
                qsortBigIsStillBig m dp = ListGTIKB10 m (fst (quicksort14 (fst dp)))

--again, using ListLEqIKB10 and ListGTIKB10 for things we do not bother to prove
--quicksort14 [3,6,45,7,2,34,6]


--------------------------------------------

-- can we get rid of IKBs?


