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


-- rewrite vars compensates for a new bound variable added...
-- all references to bound variables at the top level are incremented by 1...
-- only those on the left side of the introduced lambda are increased
rewriteVarsInf :: Int -> TermInf -> TermInf
rewriteVarsInf offset (Ann t1 t2) = Ann (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsInf offset Star = Star
rewriteVarsInf offset (Pi t1 t2) = Pi (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsInf offset (Sigma t1 t2) = Sigma (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsInf offset (Bound x) 
 | x >= offset = (Bound (x+1))
 | otherwise   = Bound x
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

rewriteVarsChk :: Int -> TermChk -> TermChk
rewriteVarsChk offset (Inf t1) = Inf (rewriteVarsInf offset t1)
rewriteVarsChk offset (Lam t1) = Lam (rewriteVarsChk offset t1)-- we need to increment the number of binds ...
rewriteVarsChk offset Zero = Zero 
rewriteVarsChk offset (Succ t1) = Succ (rewriteVarsChk offset t1)
rewriteVarsChk offset (Nil t1) = Nil (rewriteVarsChk offset t1)
rewriteVarsChk offset (Cons t1 t2 t3 t4) = Cons (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3) (rewriteVarsChk offset t4)
rewriteVarsChk offset (LNil t1) = LNil (rewriteVarsChk offset t1)
rewriteVarsChk offset (LCons t1 t2 t3) = LCons (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3)
rewriteVarsChk offset (VecToList t1 t2 t3) = VecToList (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3)
rewriteVarsChk offset (FZero t1) = FZero (rewriteVarsChk offset t1)
rewriteVarsChk offset (FSucc t1 t2) = FSucc (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsChk offset (Refl t1 t2) = Refl (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsChk offset (TNothing t1) = TNothing (rewriteVarsChk offset t1)
rewriteVarsChk offset (TJust t1 t2) = TJust (rewriteVarsChk offset t1) (rewriteVarsChk offset t2)
rewriteVarsChk offset (LTEZero t1) = LTEZero (rewriteVarsChk offset t1)
rewriteVarsChk offset (LTESucc t1 t2 t3) = LTESucc (rewriteVarsChk offset t1) (rewriteVarsChk offset t2) (rewriteVarsChk offset t3)


refacListArg :: Int -> TermChk -> TermChk
refacListArg pos (Inf (Free (Global l) :@: Inf (Bound p))) 
  | l == "List" = Inf ((Free (Global "Vec") :@: Inf (Bound p)) :@: Inf (Bound pos))
refacListArg pos x = error $ show x

refacBodyInf :: Int -> Int -> Int -> TermInf -> TermInf
refacBodyInf tot pos lamPos ((((Free (Global le) :@: p1 :@: p2) :@: p3) :@: p4) :@: Inf (Bound p))
  | le == "listElim" && p == (tot-pos) = (((Free (Global "vecElim") 
                                         :@: p1 
                                         :@: (Lam (rewriteVarsChk (countArguments 1 p2) p2))) 
                                         :@: p3) 
                                         :@: (Lam (rewriteVarsChk (countArguments 1 p4) p4))) 
                                         :@: Inf (Bound tot) 
                                         :@: Inf (Bound (tot-pos))
refacBodyInf tot p lamPos ( t1 :@: t2) = (refacBodyInf tot p lamPos t1) :@: (refacBodyChk tot p lamPos t2)
refacBodyInf tot p lamPos t = t 

refacBodyChk :: Int -> Int -> Int -> TermChk -> TermChk
refacBodyChk tot pos lamPos (Lam x)  
   = Lam (refacBodyChk tot pos (lamPos+1) x)
refacBodyChk tot pos lamPos (Inf ti) = Inf (refacBodyInf tot pos lamPos ti)
refacBodyChk _ _ _ y = y

refacPi :: Int -> Int -> TermChk -> TermChk
refacPi 1 pos2 (Inf (Pi arg bod)) = Inf (Pi (refacListArg (pos2-1) arg) bod)
refacPi pos pos2 (Inf (Pi arg bod)) = Inf (Pi arg (refacPi (pos-1) pos2 bod))
refacPi _ _ t = t

refacSig :: Stmt TermInf TermChk -> Int -> Stmt TermInf TermChk
refacSig (Let s (Ann t pi)) p = Let s (Ann (Lam (refacBodyChk (countArguments 0 t) p 1 t)) (Inf (Pi (Inf (Free (Global "Nat"))) (refacPi p p pi))))
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
