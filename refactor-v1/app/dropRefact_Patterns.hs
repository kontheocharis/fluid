module DropRefact_Patterns where

import Lang_msExt
  ( Clause (..),
    Decl (..),
    Pat (..),
    Program (Program),
    Term (..),
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



-- | The dependent drop function. TODO!!!
dropDepDecl :: Decl
dropDepDecl =
  Decl
    "dropDep"
    (PiT (var "n") NatT (PiT (var "i") (FinT (V (var "n"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n"))) (V (var "t")))))
    [ ImpossibleClause [WildP, WildP, LNilP],
      Clause [WildP, FZP, LConsP (VP (var "x")) WildP] (V (var "x")),
      Clause [SP (VP (var "n")), FSP (VP (var "f")), LConsP WildP (VP (var "xs"))] (App (App (App (Global "dropDep") (V (var "n"))) (V (var "f"))) (V (var "xs")))
    ]


--------------------------------------------------------------------------------------------------

dd1 = (PiT (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (ListT (V (var "t")))))
cl1 = Clause [ZP, (VP (var "xs")) ] (V (var "xs"))
cl2 = Clause [SP (VP (var "i")), LNilP] LNil
cl3 = Clause [SP (VP (var "i")), LConsP WildP (VP (var "xs")) ] (App (App (Global "drop") (V (var "i"))) (V (var "xs")))

--------------------------------------------------------------------------------------------------

{-
drop : (i : Nat) -> (l : List t) -> List t
drop Z xs = xs
drop (S i) [] = []
drop (S i) (_::xs) = ((drop i) xs)
-}

--------------------------------------------------------------------------------------------------
--Step 1.1: Add Nat argument before position 1
--NEED: List argument at position 2 
--n fresh


--Add (n:Nat) argument at the first position
--Future: should check that the second argument is list
addNatArgAfterOne_Decl :: Term -> Term 
addNatArgAfterOne_Decl decl = PiT (var "n") NatT decl
--now declaration has an extra n
--(n : Nat) -> (i : Nat) -> (l : List t) -> List t


--add arg to lhs of clauses
--argument2 should be list
--if arg1 is [], add ZP 
--if arg1 is Lcons, add (S n)
--if arg1 is variable, then add new var n (coudl use WildCard but it will likely cause problems later)
--must be called together with addNatArgAfterOne_Decl 
addNatArgAfterOne_clauseLHS :: Clause -> Clause
addNatArgAfterOne_clauseLHS (ImpossibleClause (arg1:(LNilP:rest))) = ImpossibleClause (ZP:(arg1:(LNilP:rest)))  
addNatArgAfterOne_clauseLHS (ImpossibleClause (arg1:((LConsP p1 p2):rest))) = ImpossibleClause ((SP (VP (var "n"))):(arg1:((LConsP p1 p2):rest))) 
addNatArgAfterOne_clauseLHS (ImpossibleClause (arg1:res)) = error "TODO: not implemented"
addNatArgAfterOne_clauseLHS (Clause (arg1:(LNilP:rest)) term) = Clause (ZP:(arg1:(LNilP:rest))) term 
addNatArgAfterOne_clauseLHS (Clause (arg1:((LConsP p1 p2):rest)) term) = Clause ((SP (VP (var "n"))):(arg1:((LConsP p1 p2):rest))) term 
addNatArgAfterOne_clauseLHS (Clause (arg1:((VP v):res)) term)  = Clause ((VP (var "n")):(arg1:((VP v):res))) term 
addNatArgAfterOne_clauseLHS (Clause (arg1:res) term) = error "TODO: not implemented"

--add arg to rhs of clauses, i.e use case, recursive case
--only works if RHS is ONLY "drop ...."
-- also update name to drop11
addNatArgAfterOne_clauseRHS :: Clause -> Clause
addNatArgAfterOne_clauseRHS (Clause patL (App (App (Global "drop") arg1) arg2)) 
  =  Clause patL (App (App (App (Global "drop11") (V (var "n"))) arg1) arg2)
addNatArgAfterOne_clauseRHS clause = clause



--acts on list of clauses
addNatArgToClauses:: [Clause] -> [Clause]
addNatArgToClauses [] = []
addNatArgToClauses (cl:cls) = ((addNatArgAfterOne_clauseRHS (addNatArgAfterOne_clauseLHS cl)):(addNatArgToClauses cls))


--acts of decl 
--also changes name to drop11
addNatArg :: Decl -> Decl
addNatArg (Decl "drop" ty clauseL) = Decl "drop11" (addNatArgAfterOne_Decl ty) (addNatArgToClauses clauseL)



--Now the clauses should have mathing Nat - Len List 

{-
drop11 : (n : Nat) -> (i : Nat) -> (l : List t) -> List t
drop11 _ Z xs = xs
drop11 Z (S i) [] = []
drop11 (S n) (S i) (_::xs) = (((drop11 n) i) xs)
-}

--Note: resulting function is not covering

--------------------------------------------------------------------------------------------------
--Step 1.2: Change List input to Vect n 

--assume type List at arg2
--change to Vect n
--here we also change var to "v", so need v fresh
listtoVectn_decl :: Term -> Term 
listtoVectn_decl (PiT lenV lenT (PiT natV natT (PiT listV (ListT ty) res))) 
   = (PiT lenV lenT (PiT natV natT (PiT (var "v") (VectT ty (V (var "n"))) res))) 
--(n : Nat) -> (i : Nat) -> (v : Vect n t) -> List t


--changes patterns, for listtoVectn_clauseLHS
--change LNilP to VNilP 
-- and LConsP to VConsP
-- otherwise remain the same
listtoVectn_pat :: Pat -> Pat 
listtoVectn_pat LNilP = VNilP
listtoVectn_pat (LConsP pat1 pat2) = VConsP pat1 pat2
listtoVectn_pat pat = pat


listtoVectn_patL :: [Pat] -> [Pat] 
listtoVectn_patL [] = []
listtoVectn_patL (x:xs) = ((listtoVectn_pat x):(listtoVectn_patL xs))


--change clause LHS
listtoVectn_clauseLHS :: Clause -> Clause 
listtoVectn_clauseLHS (Clause patL term) = Clause (listtoVectn_patL patL) term
listtoVectn_clauseLHS (ImpossibleClause patL) = ImpossibleClause (listtoVectn_patL patL) 

-- listtoVectn_decl (addNatArgAfterOne_Decl dd1)
-- listtoVectn_clauseLHS ((addNatArgAfterOne_clauseLHS cl1))
-- listtoVectn_clauseLHS ((addNatArgAfterOne_clauseLHS cl1))
-- listtoVectn_clauseLHS ((addNatArgAfterOne_clauseLHS cl2))
-- listtoVectn_clauseLHS ((addNatArgAfterOne_clauseLHS cl3))


--change clause RHS
--if the variable under the second argument (could be v itself, or xs or x:xs, or xs of x1:(x2:xs) etc etc)
--   is used in the rhs,
--need to check if it's the expected type
--e.g. if used with an operator or other functions that expects list, or as output that expects lists 
-- may need to change from vect to list (i.e. another function)
-- OR: we stick a hole in it and ask user to supply info
-- if var is used in the recursive case as input, since we are now expecting vect as input, not change is necessary
listtoVectn_clauseRHS :: Clause -> Clause 
listtoVectn_clauseRHS (Clause patL ((App (App (App (Global "drop11") arg1) arg2) arg3))) 
    = Clause patL  ((App (App (App (Global "drop12") arg1) arg2) arg3))
listtoVectn_clauseRHS (Clause (pat1: (pat2: ((VP v):patRes))) term)  
    = Clause (pat1: (pat2: ((VP v):patRes))) (subVar v (App (Global "vectToList") (V v)) term)
listtoVectn_clauseRHS cl = cl 
-- Note: most of these are not implemented. 
-- here: if right is index11 xxxx, we return as it is
-- if the arg in lhs is xs, then we replace all occurrence in rhs to (vectToList xs) 
    -- note: this is BAD. doesn't work if the rhs is a mix of recurrence and other operations (e.g. xs ++ rev xs  )
    -- also doesn't work if lhs is x:xs and rhs is xs 

listtoVectn_clauses :: [Clause] -> [Clause]
listtoVectn_clauses [] = []
listtoVectn_clauses (cl:cls) = ((listtoVectn_clauseRHS (listtoVectn_clauseLHS cl)):(listtoVectn_clauses cls))

listtoVectn :: Decl -> Decl
listtoVectn (Decl "drop11" ty clauseL) = Decl "drop12" (listtoVectn_decl ty) (listtoVectn_clauses clauseL)

{-
drop12 : (n : Nat) -> (i : Nat) -> (v : Vect n t) -> List t
drop12 n Z xs = (vectToList xs)
drop12 Z (S i) [] = []
drop12 (S n) (S i) (_::xs) = (((drop12 n) i) xs)
-}

--------------------------------------------------------------------------------------------------

-- Step 2: change output to dep type 


--change last list argument to k:Nat ** Vect k t
--need k fresh
--assume we know that there are 4 arguments 
outputToDepPair_decl :: Term -> Term 
outputToDepPair_decl (PiT lenV lenT (PiT natV natT (PiT vecV vecT output))) 
   = (PiT lenV lenT (PiT natV natT (PiT vecV vecT (SigmaT (var "k") (NatT) (VectT (V (var "t")) (V (var "k"))) ) ))) 
--(n : Nat) -> (i : Nat) -> (v : Vect n t) -> ((k : Nat) ** Vect k t)


--change rhs of clauses
--if impossible case - nothing to change
--if rhs is [], becomes Z**[]
--if rhs is vectToList xs, remove VectToList, look in lhs what is xs and change accordingly  
    -- if lhs is (n _ xs) then replace with n**xs 
    -- if lhs is ((S n) _ x::xs) then replace with n**xs 
-- if it is drop, no change needed, but change name
-- if it is application of other functions, either refactor that, or put in hole (NOT implemented yet)
-- note: correctness of this step depends on what we did in Step 1 (which gives the possible patterns in rhs)
outputToDepPair_clauseRHS :: Clause -> Clause
outputToDepPair_clauseRHS (ImpossibleClause patL) = ImpossibleClause patL
outputToDepPair_clauseRHS (Clause patL LNil) = Clause patL (MkDPair  Z VNil)
outputToDepPair_clauseRHS (Clause ((VP natV):(arg2:((VP vecV):argRes))) (App (Global "vectToList") (V rhsV))) 
    = if (vecV == rhsV) then  
        Clause ((VP natV):(arg2:((VP vecV):argRes))) (MkDPair  (V natV) (V vecV)) 
      else 
        error "TODO: not implemented"
outputToDepPair_clauseRHS (Clause ((SP (VP natV)):(arg2:((LConsP x (VP vecV)):argRes))) (App (Global "vectToList") (V rhsV))) 
    = if (vecV == rhsV) then  
        Clause ((SP (VP natV)):(arg2:((LConsP x (VP vecV) ):argRes))) (MkDPair  (V natV) (V vecV)) 
      else 
        error "TODO: not implemented"
outputToDepPair_clauseRHS (Clause patL ((App (App (App (Global "drop12") arg1) arg2) arg3))) 
    = Clause patL ((App (App (App (Global "drop2") arg1) arg2) arg3))



outputToDepPair_clauses :: [Clause] -> [Clause]
outputToDepPair_clauses [] = []
outputToDepPair_clauses (cl:cls) = ( (outputToDepPair_clauseRHS cl):(outputToDepPair_clauses cls))


outputToDepPair :: Decl -> Decl 
outputToDepPair (Decl "drop12" ty clauseL) = Decl "drop2" (outputToDepPair_decl ty) (outputToDepPair_clauses clauseL)


--outputToDepPair (listtoVectn (addNatArg dropDecl))
{-
drop2 : (n : Nat) -> (i : Nat) -> (v : Vect n t) -> (k : Nat ** Vect k t)
drop2 n Z xs = (n ** xs)
drop2 Z (S i) [] = (Z ** [])
drop2 (S n) (S i) (_::xs) = (((drop2 n) i) xs)
-}


--------------------------------------------------------------------------------------------------

--Step 3: Add proof the i<=n 


--add (p: LTE i n) after argument 2

addDomRestrictionPf_decl :: Term -> Term 
addDomRestrictionPf_decl (PiT lenV lenT (PiT natV natT res)) 
   = PiT lenV lenT (PiT natV natT (PiT (var "p") (LteT (V (var "i")) (V (var "n"))) res ))

--addDomRestrictionPf_decl (outputToDepPair_decl (listtoVectn_decl (addNatArgAfterOne_Decl dd1)))
--(n : Nat) -> (i : Nat) -> (p : LTE i n) -> (v : Vect n t) -> (k : Nat ** Vect k t)


--LTE i n is a relation on arg2 and arg1
--replace input with appropriate constructor pattern
-- if i is Z, (n can be anything), then must be LTEZero
-- if i is Succ, n is Z then replace clause with impossible
-- if both i= S i' and n=S n', then replace with LTESucc p', and we know what p' is a relation on i' and n'
-- if n is Z and i is a var, then we split (not implemented)
addDomRestrictionPf_clauseLHS :: Clause -> Clause
addDomRestrictionPf_clauseLHS (ImpossibleClause patL) = ImpossibleClause patL
addDomRestrictionPf_clauseLHS (Clause (pat:(ZP:res)) term) 
    = Clause (pat:(ZP:(LTEZeroP:res)))   term
addDomRestrictionPf_clauseLHS (Clause (ZP:((SP pat):res))   term)
    = ImpossibleClause  (ZP:((SP pat): (WildP:res)))
addDomRestrictionPf_clauseLHS (Clause ((SP pat1):((SP pat2):res)) term)
    = Clause  ((SP pat1):((SP pat2):((LTESuccP (VP (var "p'"))):res)))  term
-- addDomRestrictionPf_clauseLHS (listtoVectn_clauseLHS ((addNatArgAfterOne_clauseLHS cl1)))



--for rhs, nothing needs to change apart from the recursive case
--if lhs is (S i') and (S n') and input in the recursive call is i' and n', then we can put in p'
  -- only works if rhs is directly calling drop
--otherwise we don't know what to do and will put a hole 
addDomRestrictionPf_clauseRHS :: Clause -> Clause
addDomRestrictionPf_clauseRHS (ImpossibleClause patL) = ImpossibleClause patL
addDomRestrictionPf_clauseRHS (Clause ( (SP (VP (vnl))):((SP (VP (vil))):res))
                                      (App (App (App (Global "drop2") (V (vnr))) (V (vir))) (arg3))                                     
                              )      
    = if and [(vnl == vnr), (vil == vir)] then  
        (Clause ( (SP (VP (vnl))):((SP (VP (vil))):res))
                ((App (App (App (App (Global "drop3") (V (vnl))) (V (vil))) (V (var "p'")) ) arg3))                                     
        )
      else 
        error "TODO: not implemented"
addDomRestrictionPf_clauseRHS (Clause patL term) = Clause patL term


addDomRestrictionPf_clauses :: [Clause] -> [Clause]
addDomRestrictionPf_clauses [] = []
addDomRestrictionPf_clauses (cl:cls) = ( (addDomRestrictionPf_clauseRHS (addDomRestrictionPf_clauseLHS cl)):(addDomRestrictionPf_clauses cls))


addDomRestrictionPf :: Decl -> Decl 
addDomRestrictionPf (Decl "drop2" ty clauseL) = Decl "drop3" (addDomRestrictionPf_decl ty) (addDomRestrictionPf_clauses clauseL)

--addDomRestrictionPf (outputToDepPair (listtoVectn (addNatArg dropDecl)))
{-
drop3 : (n : Nat) -> (i : Nat) -> (p : LTE i n) -> (v : Vect n t) -> (k : Nat ** Vect k t)
drop3 n Z LTEZero xs = (n ** xs)
drop3 Z (S i) _ [] impossible
drop3 (S n) (S i) (LTESucc p') (_::xs) = ((((drop3 n) i) p') xs)
-}

--------------------------------------------------------------------------------------------------
--Step 4: lift Sigma to Pi (restrict codomain)

--add (k:Nat) and (q: k = minus n i) 
--change final arg tyl of (k:Nat ** Vect k t) to just Vect k t
removeSigma_decl :: Term -> Term 
removeSigma_decl (PiT lenV lenT (PiT natV natT (PiT lteV lteT (PiT vecV vecT (SigmaT outLenVar outLenTy outVecT) )))) 
   =  (PiT lenV lenT (PiT natV natT (PiT lteV lteT (PiT vecV vecT (PiT outLenVar outLenTy (PiT (var "q") (EqT (V (var "k")) (App (App (Global "minus") (V (var "n"))) (V (var "i")) )) outVecT )) )))) 

--removeSigma_decl (addDomRestrictionPf_decl (outputToDepPair_decl (listtoVectn_decl (addNatArgAfterOne_Decl dd1))))
--(n : Nat) -> (i : Nat) -> (p : LTE i n) -> (v : Vect n t) -> (k : Nat) -> (q : k = ((minus n) i)) -> Vect k t


--assuming that the proof is Eq 
--put in Refl in lhs of clauses
--use that to match the pattern for the k input 
removeSigma_clauseLHS :: Clause -> Clause 
removeSigma_clauseLHS (ImpossibleClause patL) = ImpossibleClause (patL ++ [WildP,WildP]) 
removeSigma_clauseLHS (Clause [arg1,arg2,arg3,arg4] term) 
    = Clause ([arg1,arg2,arg3,arg4] ++ [(AppP (AppP (GlobalP "minus") arg1 ) arg2  ), ReflP] ) term
--removeSigma_clauseLHS (addDomRestrictionPf_clauseLHS (listtoVectn_clauseLHS ((addNatArgAfterOne_clauseLHS cl1))))


--if rhs is return value (m ** vec)
  -- replace as "rewite reln in vec" and "where reln: ([lhs_arg6] = m)"
  -- but since we don't have rewrite, should put a hole 
--if rhs is recursive case (only direct rec implemented), then do as lhs  
removeSigma_clauseRHS :: Clause -> Clause 
removeSigma_clauseRHS (ImpossibleClause patL) = ImpossibleClause patL 
removeSigma_clauseRHS  (Clause [arg1,arg2,arg3,arg4,arg5,arg6] 
                               ((App (App (App (App (Global "drop3") rArg1) rArg2) rArg3 ) rArg4))  ) 
    = (Clause [arg1,arg2,arg3,arg4,arg5,arg6] 
              (App (App ((App (App (App (App (Global "drop4") rArg1) rArg2) rArg3 ) rArg4)) (App (App (Global "minus") rArg1 ) rArg2  ) )  Refl )) 
removeSigma_clauseRHS (Clause patL term) = Clause patL (Hole 1)

removeSigma_clauses :: [Clause] -> [Clause]
removeSigma_clauses [] = []
removeSigma_clauses (cl:cls) = ( (removeSigma_clauseRHS (removeSigma_clauseLHS cl)):(removeSigma_clauses cls))


removeSigma :: Decl -> Decl 
removeSigma (Decl "drop3" ty clauseL) = Decl "drop4" (removeSigma_decl ty) (removeSigma_clauses clauseL)

--removeSigma (addDomRestrictionPf (outputToDepPair (listtoVectn (addNatArg dropDecl))))
{-
drop4 : (n : Nat) -> (i : Nat) -> (p : LTE i n) -> (v : Vect n t) -> (k : Nat) -> (q : k = ((minus n) i)) -> Vect k t
drop4 n Z LTEZero xs ((minus n) Z) Refl = ?hole1
drop4 Z (S i) _ [] _ _ impossible
drop4 (S n) (S i) (LTESucc p') (_::xs) ((minus (S n)) (S i)) Refl = ((((((drop4 n) i) p') xs) ((minus n) i)) Refl)
-}

--------------------------------------------------------------------------------------------------
--Step 5: clean up: remove  (k:Nat) and (q: k = minus n i) inputs
-- change final arg to  Vect (minus n i) t

cleanUp_decl :: Term -> Term 
cleanUp_decl (PiT lenV lenT (PiT natV natT (PiT lteV lteT (PiT vecV vecT (PiT outLenVar outLenTy (PiT eqV (EqT left right) (VectT ty len) )) )))) 
 =  (PiT lenV lenT (PiT natV natT (PiT lteV lteT (PiT vecV vecT (VectT ty right ) )))) 

--cleanUp_decl (removeSigma_decl (addDomRestrictionPf_decl (outputToDepPair_decl (listtoVectn_decl (addNatArgAfterOne_Decl dd1)))))
--(n : Nat) -> (i : Nat) -> (p : LTE i n) -> (v : Vect n t) -> Vect ((minus n) i) t

cleanUp_clauseLHS :: Clause -> Clause 
cleanUp_clauseLHS (ImpossibleClause [p1,p2,p3,p4,p5,p6]) = ImpossibleClause [p1,p2,p3,p4] 
cleanUp_clauseLHS (Clause [p1,p2,p3,p4,p5,p6] term) = Clause [p1,p2,p3,p4] term

cleanUp_clauseRHS :: Clause -> Clause 
cleanUp_clauseRHS (ImpossibleClause patL) = ImpossibleClause patL 
cleanUp_clauseRHS (Clause patL (Hole m)) = Clause patL (Hole (m+1))
cleanUp_clauseRHS  (Clause patL (App (App ((App (App (App (App (Global "drop4") rArg1) rArg2) rArg3 ) rArg4)) rArg5)  rArg6 ) ) 
    = (Clause patL ((App (App (App (App (Global "drop5") rArg1) rArg2) rArg3 ) rArg4)) ) 



cleanUp_clauses :: [Clause] -> [Clause]
cleanUp_clauses [] = []
cleanUp_clauses (cl:cls) = ( (cleanUp_clauseRHS (cleanUp_clauseLHS cl)):(cleanUp_clauses cls))


cleanUp :: Decl -> Decl 
cleanUp (Decl "drop4" ty clauseL) = Decl "drop5" (cleanUp_decl ty) (cleanUp_clauses clauseL)


--cleanUp (removeSigma (addDomRestrictionPf (outputToDepPair (listtoVectn (addNatArg dropDecl)))))
{-
drop5 : (n : Nat) -> (i : Nat) -> (p : LTE i n) -> (v : Vect n t) -> Vect ((minus n) i) t
drop5 n Z LTEZero xs = ?hole2
drop5 Z (S i) _ [] impossible
drop5 (S n) (S i) (LTESucc p') (_::xs) = ((((drop5 n) i) p') xs)
-}


--------------------------------------------------------------------------------------------------

transform :: Decl -> Decl
transform _ = cleanUp (removeSigma (addDomRestrictionPf (outputToDepPair (listtoVectn (addNatArg dropDecl))))) 

main :: IO ()
main = print $ Program [dropDecl, dropDepDecl]
 
