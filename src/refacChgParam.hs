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

refacListArg :: TermChk -> TermChk
refacListArg (Inf (Free (Global l) :@: Inf (Bound p))) 
  | l == "List" = (Inf ((Free (Global "Vec") :@: Inf (Bound 0)) :@: Inf (Bound p)))
refacListArg x = error $ show x

refacPi :: Int -> TermChk -> TermChk
refacPi 1 (Inf (Pi arg bod)) = Inf (Pi (Inf (Free (Global "Nat"))) (Inf (Pi (refacListArg arg) bod)))
refacPi pos (Inf (Pi arg bod)) = Inf (Pi arg (refacPi (pos-1) bod))
refacPi _ t = t

refacSig :: Stmt TermInf TermChk -> Int -> Stmt TermInf TermChk
refacSig (Let s (Ann t pi)) p = Let s (Ann t (refacPi p pi))
refacSig _ _ = error "refactoring eror in refacSig"

refacChgParam :: String -> String -> Int -> IO ()
refacChgParam file name pos = do
    (stmts, (x,y,z)) <- typecheckandParse file
    putStrLn $ concat (map showNameValue y)
    putStrLn $ renderStmts stmts
    let term = findDef name stmts 
    putStrLn $ show term
    let term' = refacSig term pos 
    putStrLn $ renderStmt term'
