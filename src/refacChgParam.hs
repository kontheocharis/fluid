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

refacListArg :: TermChk -> TermChk
refacListArg (Inf (Free (Global l) :@: Inf (Bound p))) 
  | l == "List" = Inf ((Free (Global "Vec") :@: Inf (Bound (p+1))) :@: Inf (Bound 0))
refacListArg x = error $ show x

refacBody :: Int -> Int -> Int -> TermChk -> TermChk
refacBody tot pos lamPos (Lam x)  
  | lamPos == pos = Lam (Lam (refacBody tot pos (lamPos+1) x))
  | otherwise = Lam (refacBody tot pos (lamPos+1) x)
refacBody tot pos lamPos (Inf (((((Free (Global le) :@: p1 :@: p2) :@: p3) :@: p4) :@: Inf (Bound p)))) 
 | le == "listElim" && p == 0 = Inf ((((Free (Global "vecElim") :@: p1 :@: p2) :@: p3) :@: p4) :@: Inf (Bound (p+1)) :@: Inf (Bound p))  
refacBody _ _ _ y = y

refacPi :: Int -> TermChk -> TermChk
refacPi 1 (Inf (Pi arg bod)) = Inf (Pi (Inf (Free (Global "Nat"))) (Inf (Pi (refacListArg arg) bod)))
refacPi pos (Inf (Pi arg bod)) = Inf (Pi arg (refacPi (pos-1) bod))
refacPi _ t = t

refacSig :: Stmt TermInf TermChk -> Int -> Stmt TermInf TermChk
refacSig (Let s (Ann t pi)) p = Let s (Ann (refacBody (countArguments 0 t) p 1 t) (refacPi p pi))
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
