--quicksort (not in-place) example
--output len = input length
--using the list to vect scheme as before

import Prelude.EqOrd
import Data.Vect

--------------------------------------------

--in Idris (still simply typed)
smaller0: (Ord a) => a -> List a -> List a 
smaller0 m [] = []
smaller0 m (y::ys) = case (y <= m) of 
                      False => smaller0 m ys 
                      True => y::(smaller0 m ys)

bigger0: (Ord a) => a -> List a -> List a 
bigger0 m [] = []
bigger0 m (y::ys) = case (y > m) of 
                      False => bigger0 m ys 
                      True => y::(bigger0 m ys)

quicksort0 :  (Ord a) => List a -> List a 
quicksort0 [] = []
quicksort0 (x::xs) = quicksort0 (smaller0 x xs) ++ (x::(quicksort0 (bigger0 x xs)) )
                      
--quicksort0 [3,6,45,7,2,34,6]

--------------------------------------------

--Want to refine
--What properties do we want to encode? Maybe that the output list is the same length as the input list?
--Essentially we want to use Vect instead of list
--Then we need to prove why that's true
--requires that we know that a number if either leq m or >m
--which implies that either the number is in smaller or in bigger (need to know the simimarities between the functions!!) 
   -- maybe we want to put everything in one giant function first?

{-
quicksort1 :  (Ord a) => List a -> List a 
quicksort1 [] = []
quicksort1 (x::xs) = case xs of 
                          [] => quicksort1 [] ++ x::([])
                          (y::ys) => case ((y <= x), (y > x)) of  --product for now, but can use thm to reduce, since exactly one of them has to be true
                                        (False, False) => ?ff_qs1 -- impossible
                                        (False, True) =>  ?ft_qs1 -- quicksort1 (smaller0 y ys) + ..  --This will not work since smaller is recursive! So we can't get rid of smaller
                                        (True, False) => ?tf_qs1 
                                        (True, True) => ?tt_qs1 -- impossible
-}

--move external functions under "where"
quicksort10 :  (Ord a) => List a -> List a 
quicksort10 [] = []
quicksort10 (x::xs) = quicksort10 (smaller0 x xs) ++ (x::(quicksort10 (bigger0 x xs)) )
                        where smaller0: a -> List a -> List a 
                              smaller0 m [] = []
                              smaller0 m (y::ys) = case (y <= m) of 
                                                    False => smaller0 m ys 
                                                    True => y::(smaller0 m ys)
                              bigger0: a -> List a -> List a 
                              bigger0 m [] = []
                              bigger0 m (y::ys) = case (y > m) of 
                                                    False => bigger0 m ys 
                                                    True => y::(bigger0 m ys)

--remove params in context
quicksort12 :  (Ord a) => List a -> List a 
quicksort12 [] = []
quicksort12 (x::xs) = quicksort12 (smaller0 xs) ++ (x::(quicksort12 (bigger0 xs)) )
                        where smaller0: List a -> List a 
                              smaller0 [] = []
                              smaller0 (y::ys) = case (y <= x) of 
                                                    False => smaller0 ys 
                                                    True => y::(smaller0 ys)
                              bigger0: List a -> List a 
                              bigger0 [] = []
                              bigger0 (y::ys) = case (y > x) of 
                                                    False => bigger0 ys 
                                                    True => y::(bigger0 ys)

--user may say combine two functions as product
quicksort13 :  (Ord a) => List a -> List a 
quicksort13 [] = []
quicksort13 (x::xs) = quicksort13 (fst (smallerAndBigger0 xs)) ++ (x::(quicksort13 (snd (smallerAndBigger0 xs))) )
                        where smallerAndBigger0: List a -> (List a , List a)
                              smallerAndBigger0 [] = ([],[])
                              smallerAndBigger0 (y::ys) = 
                                  case  ((y <= x), (y > x))  of 
                                    (False, False) => (fst (smallerAndBigger0 ys),  snd (smallerAndBigger0 ys) ) -- actually impossible
                                    (False, True) =>  (fst (smallerAndBigger0 ys),  y::(snd (smallerAndBigger0 ys)) ) 
                                    (True, False) => (y::(fst (smallerAndBigger0 ys)),  snd (smallerAndBigger0 ys) )
                                    (True, True) => (y::(fst (smallerAndBigger0 ys)), y::(snd (smallerAndBigger0 ys)) ) -- impossible
--TODO: try lifting - extend LTE type?

--maybe now user would say to remove 2nd projection
quicksort14 :  (Ord a) => List a -> List a 
quicksort14 [] = []
quicksort14 (x::xs) = quicksort14 (fst (smallerAndBigger0 xs)) ++ (x::(quicksort14 (snd (smallerAndBigger0 xs))) )
                        where smallerAndBigger0: List a -> (List a ,List a)
                              smallerAndBigger0 [] = ([],[])
                              smallerAndBigger0 (y::ys) = 
                                  case  (y <= x)  of 
                                    False => (fst (smallerAndBigger0 ys),  y::(snd (smallerAndBigger0 ys)) ) 
                                    True  => (y::(fst (smallerAndBigger0 ys)),  snd (smallerAndBigger0 ys) )
                                    

--quicksort14 [3,6,45,7,2,34,6]

--------------------------------------------

--Start changing input list to vect

{-
--This will not work, since we don't know the size of the smaller and bigger lists, we only know that they add up to m
--i.e. in the recursive case, we don't have nat to input in the recursive call
--So we DP
quicksort20 :  (Ord a) => (m:Nat) -> Vect m a -> List a 
quicksort20 Z [] = []
quicksort20 (S m') (x::xs) = quicksort20 ?a (fst (smallerAndBigger0 xs)) ++ (x::(quicksort20 ?b (snd (smallerAndBigger0 xs))) )
                              where smallerAndBigger0: List a -> (List a ,List a)
                                    smallerAndBigger0 [] = ([],[])
                                    smallerAndBigger0 (y::ys) = 
                                        case  (y <= x)  of 
                                          False => (fst (smallerAndBigger0 ys),  y::(snd (smallerAndBigger0 ys)) ) 
                                          True  => (y::(fst (smallerAndBigger0 ys)),  snd (smallerAndBigger0 ys) )
                                   

--later we want (m:Nat ** (Vect m a)) -> m:Nat -> (pf: k=m) -> (k:Nat ** (Vect k a)) 
  -- so that we'll get (Vect m a) -> (Vect m a)
-}

--input is now dp
--now smallerAndBigger need to be from DP to tup of DPs
quicksort20 :  (Ord a) => (m:Nat ** (Vect m a)) -> List a   
quicksort20 (Z ** []) = []
quicksort20 ((S m') ** (x::xs)) = 
  quicksort20 (fst (smallerAndBigger0 (m' ** xs))) ++ (x::(quicksort20 (snd (smallerAndBigger0 (m' ** xs)))) ) 
    where smallerAndBigger0: (n:Nat ** (Vect n a)) -> ((k:Nat ** (Vect k a)), (l:Nat ** (Vect l a)))  --later: n=k+l
          smallerAndBigger0 (Z ** []) = ((Z ** []), (Z ** []))
          smallerAndBigger0 ((S n') ** (y::ys)) = 
              case  (y <= x)  of 
                False => ((fst (smallerAndBigger0 (n' ** ys))), 
                          (S (fst (snd (smallerAndBigger0 (n' ** ys)))) 
                            ** (y::(snd (snd (smallerAndBigger0 (n' ** ys))))) ))
                True =>  ((S (fst (fst (smallerAndBigger0 (n' ** ys)))) 
                            ** (y::(snd (fst (smallerAndBigger0 (n' ** ys))))) )  ,  
                          (snd (smallerAndBigger0 (n' ** ys))) )

--quicksort20 (7 ** [3,6,45,7,2,34,6])

--actually, we can use vectors
--only smallerAndBigger0 must use dp

--remove sigma in input
quicksort21 :  (Ord a) => (m:Nat) -> (Vect m a) -> List a   
quicksort21 Z [] = []
quicksort21 (S m') (x::xs) = 
    let small = fst (smallerAndBigger0 (m' ** xs))
        large = snd (smallerAndBigger0 (m' ** xs)) in 
          quicksort21 (fst small) (snd small) ++ (x::(quicksort21 (fst large) (snd large)) ) 
          where smallerAndBigger0: (n:Nat ** (Vect n a)) -> ((k:Nat ** (Vect k a)) ,(l:Nat ** (Vect l a)))  --later: n=k+l
                smallerAndBigger0 (Z ** []) = ((Z ** []), (Z ** []))
                smallerAndBigger0 ((S n') ** (y::ys)) = 
                  let small0 = fst (smallerAndBigger0 (n' ** ys))
                      big0 = snd (smallerAndBigger0 (n' ** ys)) in 
                        case  (y <= x)  of 
                          False => (small0, (S (fst big0) ** (y::(snd big0)) ))
                          True =>  ( (S (fst small0) ** (y::(snd small0)) )  ,  big0 )

--TODO: exists vs forall: problem?

--quicksort21 7 [3,6,45,7,2,34,6]

--------------------------------------------

--Add sigma to output

quicksort30 :  (Ord a) => (m:Nat) -> (Vect m a) -> (r:Nat ** (Vect r a))  
quicksort30 Z [] = ( Z ** [])
quicksort30 (S m') (x::xs) = 
  let small = fst (smallerAndBigger0 (m' ** xs))
      large = snd (smallerAndBigger0 (m' ** xs)) in 
        ( fst (quicksort30 (fst small) (snd small)) + ( S (fst (quicksort30 (fst large) (snd large))) ) 
          **
          snd (quicksort30 (fst small) (snd small)) ++ (x::(snd (quicksort30 (fst large) (snd large))) ) 
        )
        where smallerAndBigger0: (n:Nat ** (Vect n a)) -> ((k:Nat ** (Vect k a)), (l:Nat ** (Vect l a)))  --later: n=k+l
              smallerAndBigger0 (Z ** []) = ((Z ** []), (Z ** []))
              smallerAndBigger0 ((S n') ** (y::ys)) = 
                let small0 = fst (smallerAndBigger0 (n' ** ys))
                    big0 = snd (smallerAndBigger0 (n' ** ys)) in 
                      case  (y <= x)  of 
                        False => (small0, (S (fst big0) ** (y::(snd big0)) ))
                        True =>  ( (S (fst small0) ** (y::(snd small0)) )  ,  big0 )


--quicksort30 7 [3,6,45,7,2,34,6]


--------------------------------------------

--Add sigma to output

{-
quicksort40 :  (Ord a) => (m:Nat) -> (Vect m a) ->  (r : Nat) -> (p : r = m) -> Vect r a
quicksort40 Z [] Z Refl = []
quicksort40 (S m') (x::xs) (S m') Refl = ?rec
-}

--first we want to refac smallerAndBigger


--this didn't work
--compiler doesn't know that n-k will not be negative
{-
quicksort40 :  (Ord a) => (m:Nat) -> (Vect m a) -> (r:Nat ** (Vect r a))  
quicksort40 Z [] = ( Z ** [])
quicksort40 (S m') (x::xs) = let small = fst (smallerAndBigger0 (m' ** xs))
                                 large = snd (smallerAndBigger0 (m' ** xs)) in 
                                    ( fst (quicksort40 (fst small) (snd small)) + ( S (fst (quicksort40 (m' - fst small) (snd large))) ) 
                                      **
                                      snd (quicksort40 (fst small) (snd small)) ++ (x::(snd (quicksort40 (m' - fst small) (snd large))) ) 
                                    )
                                    where smallerAndBigger0: (n:Nat ** (Vect n a)) -> ((k:Nat ** (Vect k a)) ,( (Vect (n-k) a))) 
                                        
-}

{-
--failed attempt
quicksort40 :  (Ord a) => (m:Nat) -> (Vect m a) -> Vect m a --(r:Nat ** (Vect r a))  
quicksort40 Z [] = [] --( Z ** [])
quicksort40 (S m') (x::xs) = let small = fst (smallerAndBigger0 (m' ** xs))
                                 large = snd (smallerAndBigger0 (m' ** xs)) 
                                -- test1 = fst (quicksort40 (fst small) (snd small)) + S (fst (quicksort40 (fst large) (snd (snd large)))) 
                                -- test3 = snd (quicksort40 (fst small) (snd small)) ++ (x::(snd (quicksort40 (fst large) (snd (snd large)))) ) 
                                 ttest = fst (snd (snd (smallerAndBigger0 (m' ** xs)))) in  rewrite ttest in ?yy
                                    where smallerAndBigger0: (n:Nat ** (Vect n a)) -> (dp:(k:Nat ** Vect k a) ** (l:Nat ** ( n = (fst dp) +l, Vect l a) )) 
-}

--lenPf gives us the correct proof
quicksort40 :  (Ord a) => (m:Nat) -> (Vect m a) ->  (r : Nat) -> (p : r = m) -> Vect r a
quicksort40 Z [] Z Refl = []
quicksort40 (S m') (x::xs) (S m') Refl = 
  let --small = (fst (smallerAndBigger0 (m' ** xs)))
      --large = (snd (smallerAndBigger0 (m' ** xs))) 
      --test = snd (quicksort40 (fst small) (snd small) ) ++ (x::(snd (quicksort40 (fst large) (snd large))) ) 
      test1 =  (quicksort40 (fst  (fst (smallerAndBigger0 (m' ** xs)))) 
                            (snd  (fst (smallerAndBigger0 (m' ** xs)))) 
                            (fst  (fst (smallerAndBigger0 (m' ** xs)))) 
                            Refl ) 
      test2 =  (x::(quicksort40 (fst (snd (smallerAndBigger0 (m' ** xs))) ) 
                                (snd (snd (smallerAndBigger0 (m' ** xs))) ) 
                                (fst (snd (smallerAndBigger0 (m' ** xs))) ) 
                                Refl) ) 
      test = test1 ++ test2 
      in rewrite (lenPf m' xs) 
        in rewrite (plusSuccRightSucc (fst (fst (smallerAndBigger0 (m' ** xs)))) 
                                      (fst (snd (smallerAndBigger0 (m' ** xs)))) ) in test  
          where smallerAndBigger0: (n:Nat ** (Vect n a)) -> ((k:Nat ** (Vect k a)) ,(l:Nat ** (Vect l a)))  --later: n=k+l
                smallerAndBigger0 (Z ** []) = ((Z ** []), (Z ** []))
                smallerAndBigger0 ((S n') ** (y::ys)) = 
                  let small0 = fst (smallerAndBigger0 (n' ** ys))
                      big0 = snd (smallerAndBigger0 (n' ** ys)) in 
                        case  (y <= x)  of 
                          False => (small0, (S (fst big0) ** (y::(snd big0)) ))
                          True =>  ( (S (fst small0) ** (y::(snd small0)) )  ,  big0 )
                lenPf: (n:Nat) -> (v: Vect n a) 
                        -> n = fst (fst (smallerAndBigger0 (n ** v))) 
                                  + fst (snd (smallerAndBigger0 (n ** v)))
                lenPf n v = ?yy_qsort40



--let's change input to smallerAndBigger0 as two arg instead of dp
--then we merge smallerAndBigger0 with lenPf
quicksort41 :  (Ord a) => (m:Nat) -> (Vect m a) -> (r : Nat) -> (p : r = m) -> Vect r a
quicksort41 Z [] Z Refl = []
quicksort41 (S m') (x::xs) (S m') Refl = 
      let test1 =  (quicksort41 (fst  (fst ((fst (smallerAndBigger0 m' xs))))) 
                                (snd  (fst ((fst (smallerAndBigger0 m' xs))))) 
                                (fst  (fst ((fst (smallerAndBigger0 m' xs))))) 
                                Refl ) 
          test2 =  (x::(quicksort41 (fst (snd ((fst (smallerAndBigger0 m' xs)))) ) 
                                    (snd (snd ((fst (smallerAndBigger0 m' xs)))) ) 
                                    (fst (snd ((fst (smallerAndBigger0 m' xs)))) ) 
                                    Refl) ) 
          test = test1 ++ test2 
          in rewrite (snd (smallerAndBigger0 m' xs) ) 
            in rewrite (plusSuccRightSucc (fst (fst ((fst (smallerAndBigger0 m' xs))))) 
                                          (fst (snd ((fst (smallerAndBigger0 m' xs))))) ) in test  
              where smallerAndBigger0: (n:Nat) ->  (Vect n a) 
                                        -> (dpPair:((k:Nat ** (Vect k a)) ,(l:Nat ** (Vect l a)))  
                                            **   n = fst (fst dpPair) + fst (snd dpPair)  )
                  {-  smallerAndBigger0 Z [] = ((Z ** []), (Z ** []))
                    smallerAndBigger0 (S n') (y::ys)  = 
                      let small0 = fst (smallerAndBigger0 n' ys)
                          big0 = snd (smallerAndBigger0 n' ys) in 
                            case  (y <= x)  of 
                              False => (small0, (S (fst big0) ** (y::(snd big0)) ))
                              True =>  ( (S (fst small0) ** (y::(snd small0)) )  ,  big0 )
                  -}  

--TODO:  (k:Nat ** (l:Nat ** (Vect k a, Vect l a, proof) ) )
-- Document the types of refactoring sketch


--Q: this is alot of work. How is this ever useful to a programmer?
  --maybe we want to use the result of quicksort somewhere and it's absolutely critical that the length is correct?

--Q: how does lifting with ornaments work with quicksort?? 
  --how can we know that the resulting length is the same as the input length? 
  --would need to know that <=m or >m 


--now we complete smallerAndBigger0         
quicksort42 :  (Ord a) => (m:Nat) -> (Vect m a) -> (r : Nat) -> (p : r = m) -> Vect r a
quicksort42 Z [] Z Refl = []
quicksort42 (S m') (x::xs) (S m') Refl = 
  let test1 =  (quicksort42 (fst  (fst ((fst (smallerAndBigger0 m' xs))))) 
                            (snd  (fst ((fst (smallerAndBigger0 m' xs))))) 
                            (fst  (fst ((fst (smallerAndBigger0 m' xs))))) 
                            Refl ) 
      test2 =  (x::(quicksort42 (fst (snd ((fst (smallerAndBigger0 m' xs)))) ) 
                                (snd (snd ((fst (smallerAndBigger0 m' xs)))) ) 
                                (fst (snd ((fst (smallerAndBigger0 m' xs)))) ) 
                                Refl) ) 
      test = test1 ++ test2 
      in rewrite (snd (smallerAndBigger0 m' xs) ) 
        in rewrite (plusSuccRightSucc (fst (fst ((fst (smallerAndBigger0 m' xs))))) 
                                      (fst (snd ((fst (smallerAndBigger0 m' xs))))) ) in test  
          where smallerAndBigger0: (n:Nat) ->  (Vect n a) 
                                    -> (dpPair:((k:Nat ** (Vect k a)) ,(l:Nat ** (Vect l a)))  
                                        **   n = fst (fst dpPair) + fst (snd dpPair)  )
                smallerAndBigger0 Z [] = (((Z ** []), (Z ** [])) ** Refl )
                smallerAndBigger0 (S n') (y::ys)  = 
                  let   recRes = (smallerAndBigger0 n' ys)
                  --    small0 = (fst (fst (smallerAndBigger0 n' ys)))
                  --    big0 = (snd (fst (smallerAndBigger0 n' ys)))
                  --    pf0 = snd (smallerAndBigger0 n' ys) 
                  --    --succpf0 = (eqSucc n' (fst (fst (fst (smallerAndBigger0 n' ys) )) + fst (snd (fst (smallerAndBigger0 n' ys) )) ) pf0) 
                      in 
                        case  (y <= x)  of 
                          False => ( ((fst (fst recRes)), (S (fst (snd (fst recRes))) ** (y::(snd (snd (fst recRes)))) )) 
                                      ** rewrite (sym (plusSuccRightSucc (fst (fst (fst recRes))) (fst (snd (fst recRes))))) in 
                                          (eqSucc n' (fst (fst (fst recRes)) + fst (snd (fst recRes)) )  (snd recRes)) ) 
                          True => ( ( (S (fst (fst (fst recRes))) ** (y::(snd (fst (fst recRes)))) )  ,  (snd (fst recRes)) ) 
                                    ** (eqSucc n' (fst (fst (fst recRes )) + fst (snd (fst recRes )) )  (snd recRes ) )  )

--remove duplicate recursive calls for efficiency

--quicksort42 3 [3,6,2] 3 Refl
--quicksort42 4 [3,6,7,2] 4 Refl
--quicksort42 5 [3,8,6,7,2] 5 Refl  

--quicksort42 7 [3,6,45,7,2,34,6] 7 Refl


--------------------------------------------
 
--remove pf obligations 

quicksort50 :  (Ord a) => (m:Nat) -> (Vect m a) ->  Vect m a
quicksort50 Z [] = []
quicksort50 (S m') (x::xs) = 
  let test1 =  (quicksort50 (fst  (fst ((fst (smallerAndBigger0 m' xs))))) 
                            (snd  (fst ((fst (smallerAndBigger0 m' xs)))))  ) 
      test2 =  (x::(quicksort50 (fst (snd ((fst (smallerAndBigger0 m' xs)))) ) 
                                (snd (snd ((fst (smallerAndBigger0 m' xs)))) ) ) ) 
      test = test1 ++ test2 
      in rewrite (snd (smallerAndBigger0 m' xs) ) 
        in rewrite (plusSuccRightSucc (fst (fst ((fst (smallerAndBigger0 m' xs))))) 
                                      (fst (snd ((fst (smallerAndBigger0 m' xs))))) ) in test  
          where smallerAndBigger0: (n:Nat) ->  (Vect n a) 
                                    -> (dpPair:((k:Nat ** (Vect k a)) ,(l:Nat ** (Vect l a))) 
                                        **   n = fst (fst dpPair) + fst (snd dpPair)  )
                smallerAndBigger0 Z [] = (((Z ** []), (Z ** [])) ** Refl )
                smallerAndBigger0 (S n') (y::ys)  = 
                  let recRes = (smallerAndBigger0 n' ys)
                    in case  (y <= x)  of 
                        False => ( ((fst (fst recRes)), (S (fst (snd (fst recRes))) ** (y::(snd (snd (fst recRes)))) )) 
                                    ** rewrite (sym (plusSuccRightSucc (fst (fst (fst recRes))) (fst (snd (fst recRes))))) in 
                                        (eqSucc n' (fst (fst (fst recRes)) + fst (snd (fst recRes)) )  (snd recRes)) ) 
                        True => ( ( (S (fst (fst (fst recRes))) ** (y::(snd (fst (fst recRes)))) )  ,  (snd (fst recRes)) ) 
                                  ** (eqSucc n' (fst (fst (fst recRes )) + fst (snd (fst recRes )) )  (snd recRes ) )  )


--TODO: pattern match on recRes to get rid of projections 
-- have small lemmas

--quicksort50 7 [3,6,45,7,2,34,6]

--TODO: better abstractions to avoid the fst and snds?


--TODO: got ot hare webpage
--https://www.cs.kent.ac.uk/projects/refactor-fp/catalogue/ConsOrcons.html

--projection to pattern match !! 
--merging dp params
--tf thing