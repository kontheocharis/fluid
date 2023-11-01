module DropRefact where

import Lang_msExt
  ( Clause (..),
    Decl (..),
    Pat (..),
    Program (Program),
    Term (..),
    Type
  )
import Vars (var, subVar)

-- | The non-dependent drop function.
dropDecl :: Decl
dropDecl =
  Decl
    "drop"
    (PiT (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (ListT (V (var "t")))))
    [ Clause [ZP, (VP (var "xs")) ] (V (var "xs")),
      Clause [SP (VP (var "i")), LNilP] LNil,
      Clause [SP (VP (var "i")), LConsP WildP (VP (var "xs")) ] (App (App (Global "drop") (V (var "i"))) (V (var "xs")))
    ]

--------------------------------------------------------------------------------------------------
dd = (PiT (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (ListT (V (var "t")))))
cl1 = Clause [ZP, (VP (var "xs")) ] (V (var "xs"))
cl2 = Clause [SP (VP (var "i")), LNilP] LNil
cl3 = Clause [SP (VP (var "i")), LConsP WildP (VP (var "xs")) ] (App (App (Global "drop") (V (var "i"))) (V (var "xs")))
--------------------------------------------------------------------------------------------------

insertAt :: a -> Int -> [a] -> [a]
insertAt newElement 0 as = newElement:as
insertAt newElement i (a:as) = a : insertAt newElement (i - 1) as

-- |Add (v : Ty) argument at the ith position of a type signature
-- @param int: i 
-- @param String: variable name v
-- @param Type: type of param
-- @param term: the signature of the function
addArgAt_Decl :: Int -> String -> Type -> Term  -> Term 
addArgAt_Decl 0 str ty term = PiT (var str) ty term
addArgAt_Decl i str ty (PiT v t res) = PiT v t (addArgAt_Decl (i-1) str ty res)

-- |Add Nat param pattern at position ith, accoding to the list param pattern in a clause   
-- @param int: new position of Nat param 
-- @param int: position of list param 
-- @param clause: the clause to change
addNatArgAt_clauseLHS :: Int -> Int -> Clause -> Clause
addNatArgAt_clauseLHS i listInd (ImpossibleClause patL) = 
    case patL!!listInd of
        LNilP -> ImpossibleClause (insertAt ZP i patL)  
        LConsP p1 p2 -> ImpossibleClause (insertAt (SP (VP (var "n"))) i patL)   
        VP v -> ImpossibleClause (insertAt (VP (var "n")) i patL) 
addNatArgAt_clauseLHS i listInd (Clause patL term) = 
    case patL!!listInd of
        LNilP -> Clause (insertAt ZP i patL) term 
        LConsP p1 p2 -> Clause (insertAt (SP (VP (var "n"))) i patL) term
        VP v -> Clause (insertAt (VP (var "n")) i patL) term


-- check if given term is the (full) application of function of the given name 
-- @param String: name of function
-- @param Int: number of parameters of the function
-- @param Int: the term in question
checkTermIsFunc :: String -> Int -> Term -> Bool    
checkTermIsFunc fname 1 term = 
    case term of 
        App (Global fname) arg -> True 
        _ -> False 
checkTermIsFunc fname i term =
    case term of 
        App (App fname' arg') arg -> checkTermIsFunc fname (i-1) (App fname' arg')
        _ -> False

-- get i-th parameter of term, where term is a application of function
-- @param Int: i
-- @param Int: number of parameters of the function
-- @param Term: the term in question, where checkTermIsFunc term should be true
getIthParam :: Int -> Int -> Term -> Term
getIthParam i j term =
    if (j-i) == 1 then 
        case term of 
            App func arg -> arg
        else         
        case term of 
            App func arg -> getIthParam i (j-1) func

-- add param at position i, where term is a application of function  
-- @param Int: i
-- @param Term: the term to add as param
-- @param Int: number of parameters of the function
-- @param Term: the term in question, where checkTermIsFunc term should be true
addParamAt :: Int -> Term -> Int -> Term -> Term
addParamAt i param j term =
    if (j-i) == 0 then 
        case term of 
            App func arg -> App (App func param) arg
    else         
        case term of 
            App func arg -> App (addParamAt i param (j-1) func) arg 

-- given a term representing the application of function name, replace name with new name 
-- @param Term: the term to edit
-- @param Int: number of params of func
-- @param String: original name of function 
-- @param String: new name 
-- @param Term: the term in question, where checkTermIsFunc term should be true
changeAppFname :: Term -> Int -> String -> String -> Term 
changeAppFname term 1 str1 str2 = 
    case term of 
        App (Global str1) arg -> App (Global str2) arg 
changeAppFname term i str1 str2 =
    case term of 
        App res arg -> App (changeAppFname res (i-1) str1 str2) arg



-- Add Nat param to the recursive function call at position i, according to the list param pattern of said function call 
-- @param int: new position of Nat param 
-- @param int: position of list param (before adding new param)
-- @param int: number of parameters of function, before adding new  
-- @param clause: the clause to change. Only works if rhs is a recursive function call, otherwise put hole/ return as it is
addNatParam_clauseRHS :: Int -> Int -> Int -> Clause -> Clause
addNatParam_clauseRHS _ _ _ (ImpossibleClause patL) = ImpossibleClause patL
addNatParam_clauseRHS i j k (Clause patL term) = 
    if checkTermIsFunc "drop" 2 term then      
        case (patL!!i, patL!!(j+1), getIthParam j k term) of 
            ((SP (VP nVar) ) , LConsP x (VP xs1), V xs2) ->      
                if (xs1 == xs2) then                             -- drop (S n) _ (_::xs)  =  drop _ xs 
                    Clause patL (changeAppFname (addParamAt i (V nVar) j term) (k+1) "drop" "drop11" ) 
                                                                 -- rhs becomes: drop11 n _ xs                     
                else                                             
                    (Clause patL (Hole "addNat"))                
    else                                                         -- not a recursive call, so no change needed
        Clause patL term               

-- TODO: find and replace term in clause rhs 

addNatParam_clauses:: [Clause] -> [Clause]
addNatParam_clauses [] = []
addNatParam_clauses (cl:cls) = 
    ((addNatParam_clauseRHS 0 1 2 
                            (addNatArgAt_clauseLHS 0 1 cl)
     ):(addNatParam_clauses cls))


addNatParam :: Decl -> Decl
addNatParam (Decl "drop" sig clauseL) = Decl "drop11" 
                                              (addArgAt_Decl 0 "n" NatT sig) 
                                              (addNatParam_clauses clauseL)

{-
--addNatParam dropDecl
drop11 : (n : Nat) -> (i : Nat) -> (l : List t) -> List t
drop11 n Z xs = xs
drop11 Z (S i) [] = []
drop11 (S n) (S i) (_::xs) = (((drop11 n) i) xs)
-}


-- change List param ith position of a type signature into a "Vect n"
-- @param int: i 
-- @param String: variable name n
-- @param String: new var name for the vect param
-- @param term: the signature of the function
listToVectAt_Decl :: Int -> String -> String -> Term -> Term 
listToVectAt_Decl 0 str vecV (PiT v (ListT ty) res) =  
    (PiT (var vecV) (VectT ty (V (var str))) res)
listToVectAt_Decl i str vecV (PiT v t res) = 
    PiT v t (listToVectAt_Decl (i-1) str vecV res)
--listToVectAt_Decl 2 "n" "v" (addArgAt_Decl 0 "n" NatT dd) 


replaceAt :: Int -> t -> [t] -> [t]
replaceAt 0 y (x:xs) = y:xs  
replaceAt i y (x:xs) = x:(replaceAt (i-1) y xs)

-- change List param ith position of the lhs of clauses to Vects
-- @param int: i 
-- @param clause: the clause to change
listToVectAt_clauseLHS :: Int -> Clause -> Clause 
listToVectAt_clauseLHS i (ImpossibleClause patL) = 
    case patL!!i of 
        LNilP -> ImpossibleClause (replaceAt i VNilP patL)
        LConsP pat1 pat2 -> ImpossibleClause (replaceAt i (VConsP pat1 pat2) patL) 
        _ -> ImpossibleClause patL
listToVectAt_clauseLHS i (Clause patL term) = 
    case patL!!i of 
        LNilP -> Clause (replaceAt i VNilP patL) term
        LConsP pat1 pat2 -> Clause (replaceAt i (VConsP pat1 pat2) patL) term
        _ -> Clause patL term


listToVectAt_termRHS :: Pat -> Term -> Term 
listToVectAt_termRHS pat (V v) = 
    case pat of 
        VP w -> if w==v then 
                    (App (Global "vectToList") (V v) )
                else 
                    (V v) 
        LConsP x xs -> listToVectAt_termRHS xs (V v) 
        LNilP -> (V v) 

-- update ths of clauses when the i-th param list becomes vect
-- @param int: position of changed list->vect param 
-- @param int: number of params of func
-- @param clause: the clause to change
--Assumption 1: that the output is a List
--Assumption 2: VectToList is available
listToVectAt_clauseRHS :: Int -> Int -> Clause -> Clause
listToVectAt_clauseRHS i j (ImpossibleClause patL) = ImpossibleClause patL
listToVectAt_clauseRHS i j (Clause patL term) = 
    case term of 
        App res t2 -> 
            if checkTermIsFunc "drop11" 3 term then -- recursive call, no change needed, apart from changing name
                Clause patL (changeAppFname term 3 "drop11" "drop12")
            else                                    -- application of other functions, put hole
                Clause patL (Hole "listToVectRHS")
        LNil -> Clause patL term                    -- is a list anyway, so no change needed
        LCons x xs ->  Clause patL (LCons x (App (Global "vectToList") xs )) 
                                                    -- rhs is _:xs, but now xs is vect, so replace with (vectToList xs)
        V v -> Clause patL (listToVectAt_termRHS (patL!!i) term )
            




listToVectInput_clauses:: [Clause] -> [Clause]
listToVectInput_clauses [] = []
listToVectInput_clauses (cl:cls) = 
    ((listToVectAt_clauseRHS 2 3
                            (listToVectAt_clauseLHS 2 cl)
     ):(listToVectInput_clauses cls))


listToVectInput :: Decl -> Decl
listToVectInput (Decl "drop11" sig clauseL) = Decl "drop12" 
                                                    (listToVectAt_Decl 2 "n" "v" sig) 
                                                    (listToVectInput_clauses clauseL)


-------------------------------------------------

main :: IO ()
main = do { print "\n"
            ;print dropDecl
            ;print "--------------"
            ;print (addNatParam dropDecl)
            ;print "--------------"
            ;print (listToVectInput (addNatParam dropDecl)   )             
          } 