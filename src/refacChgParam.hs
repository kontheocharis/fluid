module RefacChgParam where

import Utils

import REPL

import Syntax
import Eval
import Typecheck
-- import LambdaPi.Quote
import Parser
import Pretty

import Text.PrettyPrint.HughesPJ hiding (parens)

findDef :: String -> [Stmt TermInf TermChk] -> Stmt TermInf TermChk
findDef name [] = error "Cannot find definition."
findDef name (Let s a : stmts) 
    | name == s = Let s a 
    | otherwise = findDef name stmts
findDef name (s : stmts) = findDef name stmts

-- (Ann (Lam (Lam (Lam (Lam (Inf (((((Free (Global "listElim") :@: Inf (Bound 3)) :@: Lam (Inf (Free (Global "List") :@: Inf (Bound 3)))) :@: Inf (Free (Global "LNil") :@: Inf (Bound 2))) :@: Lam (Lam (Lam (Inf (((Free (Global "LCons") :@: Inf (Bound 5)) :@: Inf (Bound 4 :@: Inf (Bound 2))) :@: Inf (Bound 0)))))) :@: Inf (Bound 0)))))))

countArguments :: Int -> TermChk -> Int
countArguments p (Lam x) = countArguments (p+1) x 
countArguments p _ = p

{-
-- rewrite vars compensates for a new bound variable added...
-- all references to bound variables at the top level are incremented by 1...
-- only those on the left side of the introduced lambda are increased
rewriteVarsInf :: Int -> TermInf -> TermInf
rewriteVarsInf offset (Ann t1 t2) = Ann (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsInf offset Star = Star
rewriteVarsInf offset (Pi t1 t2) = Pi (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsInf offset (Sigma t1 t2) = Sigma (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsInf offset (Bound x) = (Bound (x+offset))
rewriteVarsInf offset (Free n) = Free n 
rewriteVarsInf offset (ti :@: tc) = (rewriteVarsInf offset ti) :@: (rewriteVarsChk offset tc)
rewriteVarsInf offset (App t1 t2) = App (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsInf offset (Pair t1 t2 t3 t4) = Pair (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4)
rewriteVarsInf offset Nat = Nat
rewriteVarsInf offset (NatElim t1 t2 t3 t4) = NatElim (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4)
rewriteVarsInf offset (Vec t1 t2) = Vec (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsInf offset (VecElim t1 t2 t3 t4 t5 t6) = VecElim (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5) (rewriteVarsChk offset t6)
rewriteVarsInf offset (List t1) = List (rewriteVarsChk offset t1)
rewriteVarsInf offset (ListElim t1 t2 t3 t4 t5) = ListElim (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5)
rewriteVarsInf offset (Fin t1) = Fin (rewriteVarsChk offset t1)
rewriteVarsInf offset (FinElim t1 t2 t3 t4 t5) = FinElim (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5)
rewriteVarsInf offset (Eq t1 t2 t3) = Eq (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3)
rewriteVarsInf offset (EqElim t1 t2 t3 t4 t5 t6) = EqElim (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5) (rewriteVarsChk offset t6)
rewriteVarsInf offset (SigElim t1 t2 t3 t4 t5) = SigElim (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5)
rewriteVarsInf offset (TMaybe t1) = TMaybe (rewriteVarsChk offset t1)
rewriteVarsInf offset (LTE t1 t2) = LTE (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsInf offset (LTEElim t1 t2 t3 t4 t5 t6) = LTEElim (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4) (rewriteVarsChk offset t5) (rewriteVarsChk offset t6)
-}

{-
data TermChk =         
   Inf TermInf          -- CHK
 | Lam TermChk          -- LAM
 | Zero
 | Succ TermChk 
 | Nil TermChk
 | Cons TermChk TermChk TermChk TermChk
 | LNil TermChk         -- List Nil
 | LCons TermChk TermChk TermChk -- List Cons
 | VecToList TermChk TermChk TermChk
 | FZero TermChk
 | FSucc TermChk TermChk
 | Refl TermChk TermChk
 | TNothing TermChk
 | TJust TermChk TermChk
 | LTEZero TermChk 
 | LTESucc TermChk TermChk TermChk
-}
{-
rewriteVarsChk :: Int -> TermChk -> TermChk
rewriteVarsChk offset (Inf t1) = Inf (rewriteVarsInf t1)
rewriteVarsChk offset (Lam t1) = error "lambda case" -- we need to increment the number of binds ...
rewriteVarsChk offset Zero = Zero 
rewriteVarsChk offset (Succ t1) = Succ (rewriteVarsChk t1)
rewriteVarsChk offset (Nil t1) = Nil (rewriteVarsChk t1)
rewriteVarsChk offset (Cons t1 t2 t3 t4) = Cons (rewriteVarsChk t1) (rewriteVarsChk t2) (rewriteVarsChk t3) (rewriteVarsChk t4)
rewriteVarsChk offset (LNil t1) = LNil (rewriteVarsChk t1)
rewriteVarsChk offset (LCons t1 t2 t3) = LCons (rewriteVarsChk t1) (rewriteVarsChk t2) (rewriteVarsChk t3)
rewriteVarsChk offset (VecToList t1 t2 t3) = VecToList (rewriteVarsChk t1) (rewriteVarsChk t2) (rewriteVarsChk t3)
rewriteVarsChk offset (FZero t1) = FZero (rewriteVarsChk t1)
rewriteVarsChk offset (FSucc t1 t2) = FSucc (rewriteVarsChk t1) (rewriteVarsChk t2)
rewriteVarsChk offset (Refl t1 t2) = Refl (rewriteVarsChk t1) (rewriteVarsChk t2)
rewriteVarsChk offset (TNothing t1) = TNothing (rewriteVarsChk t1)
rewriteVarsChk offset (TJust t1 t2) = TJust (rewriteVarsChk t1) (rewriteVarsChk t2)
rewriteVarsChk offset (LTEZero t1) = LTEZero (rewriteVarsChk t1)
rewriteVarsChk offset (LTESucc t1 t2 t3) = LTESucc (rewriteVarsChk t1) (rewriteVarsChk t2) (rewriteVarsChk t3)
-}

refacListArg :: TermChk -> TermChk
refacListArg (Inf (Free (Global l) :@: Inf (Bound p))) 
  | l == "List" = Inf ((Free (Global "Vec") :@: Inf (Bound (p+1))) :@: Inf (Bound 0))
refacListArg x = error $ show x

refacBody :: Int -> Int -> Int -> TermChk -> TermChk
refacBody tot pos lamPos (Lam x)  
   = Lam (refacBody tot pos (lamPos+1) x)
refacBody tot pos lamPos (Inf (((((Free (Global le) :@: p1 :@: p2) :@: p3) :@: p4) :@: Inf (Bound p)))) 
 | le == "listElim" && p == 0 = Inf ((((Free (Global "vecElim") :@: p1 :@: p2) :@: p3) :@: p4) :@: Inf (Bound tot) :@: Inf (Bound p))  
refacBody _ _ _ y = y

refacPi :: Int -> TermChk -> TermChk
refacPi 1 (Inf (Pi arg bod)) = Inf (Pi (refacListArg arg) bod)
refacPi pos (Inf (Pi arg bod)) = Inf (Pi arg (refacPi (pos-1) bod))
refacPi _ t = t

refacSig :: Stmt TermInf TermChk -> Int -> Stmt TermInf TermChk
refacSig (Let s (Ann t pi)) p = Let s (Ann (Lam (refacBody (countArguments 0 t) p 1 t)) (Inf (Pi (Inf (Free (Global "Nat"))) (refacPi p pi))))
refacSig _ _ = error "refactoring eror in refacSig"

refacChgParam :: String -> String -> Int -> IO ()
refacChgParam file name pos = do
    (stmts, (x,y,z)) <- typecheckandParse file
    putStrLn $ concatMap showNameValue y
    putStrLn $ renderStmts stmts
    let term = findDef name stmts 
    putStrLn $ show term
    let term' = refacSig term pos 
    putStrLn $ renderStmt term'
