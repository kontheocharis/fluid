module Utils where

-- import Common
import REPL

import Syntax
import Eval
import Typecheck
-- import LambdaPi.Quote
import Parser
import Pretty

import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language

showNameValue :: (Name, Value) -> String
showNameValue (n, v) = show n ++ render (cPrint_ 0 0 (quote0 v)) ++ "\n"

lpte :: Context
lpte =      [(Global "Zero", VNat),
             (Global "Succ", VPi VNat (\ _ -> VNat)),
             (Global "Nat", VStar),
             (Global "natElim", VPi (VPi VNat (\ _ -> VStar)) (\ m ->
                               VPi (m `vapp` VZero) (\ _ ->
                               VPi (VPi VNat (\ k -> VPi (m `vapp` k) (\ _ -> (m `vapp` (VSucc k))))) ( \ _ ->
                               VPi VNat (\ n -> m `vapp` n))))),
             (Global "Nil", VPi VStar (\ a -> VVec a VZero)),
             (Global "Cons", VPi VStar (\ a ->
                            VPi VNat (\ n ->
                            VPi a (\ _ -> VPi (VVec a n) (\ _ -> VVec a (VSucc n)))))),
             (Global "Vec", VPi VStar (\ _ -> VPi VNat (\ _ -> VStar))),
             (Global "vecElim", VPi VStar (\ a ->
                               VPi (VPi VNat (\ n -> VPi (VVec a n) (\ _ -> VStar))) (\ m ->
                               VPi (m `vapp` VZero `vapp` (VNil a)) (\ _ ->
                               VPi (VPi VNat (\ n ->
                                     VPi a (\ x ->
                                     VPi (VVec a n) (\ xs ->
                                     VPi (m `vapp` n `vapp` xs) (\ _ ->
                                     m `vapp` VSucc n `vapp` VCons a n x xs))))) (\ _ ->
                               VPi VNat (\ n ->
                               VPi (VVec a n) (\ xs -> m `vapp` n `vapp` xs))))))),
             (Global "LNil", VPi VStar (\ a -> VList a)),
             (Global "LCons", VPi VStar (\ a ->
                            VPi a (\ _ -> VPi (VList a) (\ _ -> VList a )))),
             (Global "List", VPi VStar (\ _ -> VStar)),

             (Global "Maybe", VPi VStar (\ _ -> VStar)),

             (Global "Nothing", VPi VStar (\a -> VMaybe a)),

             (Global "Just", VPi VStar (\a ->
                               VPi a (\ _ -> VMaybe a))),

             -- (Global "Sigma", VPi VStar (\a -> VPi a (\_ -> VStar))), 

             (Global "Sigma", VPi VStar (\a -> (VPi (VPi a (\_ -> VStar)) (\_ -> VStar)))),

             (Global "Pair", VPi VStar (\a -> 
                                          VPi a (\x -> 
                                                  VPi (VPi a (\_ -> VStar)) (\p ->
                                                   VPi (p `vapp` x) (\_ -> VSigma a p))))),

             (Global "listElim", VPi VStar (\ a ->
                               VPi (VPi (VList a) (\ _ -> VStar)) (\ m ->
                               VPi (m `vapp` (VLNil a)) (\ _ ->
                               VPi (VPi a (\ x ->
                                     VPi (VList a) (\ xs ->
                                     VPi (m `vapp` xs) (\ _ ->
                                     m `vapp` VLCons a x xs)))) (\ _ ->
                               VPi (VList a) (\ xs -> m `vapp` xs)))))),

             (Global "sigElim", VPi VStar (\a -> 
                                  VPi 
                                      (VPi a (\_ -> VStar)) (\f ->
                                        VPi 
                                          (VPi (VSigma a (f `vapp` a)) (\_ -> VStar)) (\z ->
                                             VPi 
                                                (VPi a (\w -> VPi (f `vapp` w) (\g -> z `vapp` (VSigma w g))))
                                                  (\_ ->
                                                   VPi 
                                                    (VSigma a f) 
                                                     (\k -> z `vapp` k)))))),


             (Global "vecToList", VPi VStar ( \ a -> (VPi VNat ( \n -> (VPi (VVec a n) (\v -> VList a))))))  ,

             (Global "Refl", VPi VStar (\ a -> VPi a (\ x ->
                            VEq a x x))),
             (Global "Eq", VPi VStar (\ a -> VPi a (\ x -> VPi a (\ y -> VStar)))),
             (Global "eqElim", VPi VStar (\ a ->
                              VPi (VPi a (\ x -> VPi a (\ y -> VPi (VEq a x y) (\ _ -> VStar)))) (\ m ->
                              VPi (VPi a (\ x -> ((m `vapp` x) `vapp` x) `vapp` VRefl a x)) (\ _ ->
                              VPi a (\ x -> VPi a (\ y ->
                              VPi (VEq a x y) (\ eq ->
                              ((m `vapp` x) `vapp` y) `vapp` eq))))))),

             (Global "LTE", VPi VNat (\ l -> VPi VNat ( \ r -> VStar))),
             (Global "LTEZero", VPi VNat (\ r -> VLTE VZero r)),
             (Global "LTESucc", VPi VNat (\ l -> 
                                   VPi VNat (\ r -> 
                                     VPi (VLTE l r) (\lte -> 
                                        VLTE (VSucc l) (VSucc r))))),


             (Global "lteElim", VPi (VPi VNat (\l -> VPi VNat (\r -> VPi (VLTE l r) (\lte -> VStar)))) (\x -> 
                                  VPi (VPi VNat (\r -> x `vapp` VZero `vapp` r `vapp` (VLTEZero r))) (\z ->
                                     VPi (VPi VNat (\left -> (VPi VNat (\right -> (VPi (VLTE left right) (\l -> VPi (x `vapp` left `vapp` right `vapp` l) (\_ -> x `vapp` (VSucc left) `vapp` (VSucc right) `vapp` (VLTESucc left right l)))))))) (\nz ->
                                          VPi VNat (\l -> 
                                           VPi VNat (\r -> 
                                            VPi (VLTE l r) (\lte -> x `vapp` l `vapp` r `vapp` lte)))))) ),


             (Global "FZero", VPi VNat (\ n -> VFin (VSucc n))),
             (Global "FSucc", VPi VNat (\ n -> VPi (VFin n) (\ f ->
                               VFin (VSucc n)))),
             (Global "Fin", VPi VNat (\ n -> VStar)),
             (Global "finElim", VPi (VPi VNat (\ n -> VPi (VFin n) (\ _ -> VStar))) (\ m ->
                               VPi (VPi VNat (\ n -> m `vapp` (VSucc n) `vapp` (VFZero n))) (\ _ ->
                               VPi (VPi VNat (\ n -> VPi (VFin n) (\ f -> VPi (m `vapp` n `vapp` f) (\ _ -> m `vapp` (VSucc n) `vapp` (VFSucc n f))))) (\ _ ->
                               VPi VNat (\ n -> VPi (VFin n) (\ f ->
                               m `vapp` n `vapp` f))))))]
          --  ]

lpve :: Context
lpve =      [(Global "Zero", VZero),
             (Global "Succ", VLam (\ n -> VSucc n)),
             (Global "Nat", VNat),
             (Global "natElim", evalChk (Lam (Lam (Lam (Lam (Inf (NatElim (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))) ([],[])),
             (Global "Maybe", VLam (\a -> VMaybe a)),
             (Global "Nothing", VLam (\a -> VNothing a)),
             (Global "Just" , VLam (\a -> VLam ( \ b -> VJust a b))),
             (Global "Nil", VLam (\ a -> VNil a)),
             (Global "LNil", VLam (\ a -> VLNil a)),
             (Global "Cons", VLam (\ a -> VLam (\ n -> VLam (\ x -> VLam (\ xs ->
                            VCons a n x xs))))),
             (Global "LCons", VLam (\ a -> VLam (\ x -> VLam (\ xs ->
                            VLCons a x xs)))),
             (Global "Vec", VLam (\ a -> VLam (\ n -> VVec a n))),
             (Global "List", VLam (\ a -> VList a )),
             (Global "Sigma", VLam (\ a -> VLam (\f -> VSigma a f))),
             (Global "Pair", VLam (\x -> VLam (\y -> VLam (\z -> VLam (\a -> VPair x y z a))))), 
             (Global "vecToList", VLam (\a -> VLam (\ n -> VLam (\v -> VList a)))),
             (Global "vecElim", evalChk (Lam (Lam (Lam (Lam (Lam (Lam (Inf (VecElim (Inf (Bound 5)) (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))))) ([],[])),
             (Global "listElim", evalChk (Lam (Lam (Lam (Lam (Lam (Inf (ListElim (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0))))))))) ([],[])),
             (Global "Refl", VLam (\ a -> VLam (\ x -> VRefl a x))),
             (Global "Eq", VLam (\ a -> VLam (\ x -> VLam (\ y -> VEq a x y)))),
             (Global "eqElim", evalChk (Lam (Lam (Lam (Lam (Lam (Lam (Inf (EqElim (Inf (Bound 5)) (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))))) ([],[])),
             (Global "sigElim", evalChk (Lam (Lam (Lam (Lam (Lam (Inf (SigElim (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0))))))))) ([],[])),
             (Global "LTE", VLam (\l -> VLam (\r -> VLTE l r))),
             (Global "LTEZero", VLam (\r -> VLTEZero r)),
             (Global "LTESucc", VLam (\l -> VLam (\r -> VLam (\lte -> VLTESucc l r lte)))),

             (Global "FZero", VLam (\ n -> VFZero n)),
             (Global "FSucc", VLam (\ n -> VLam (\ f -> VFSucc n f))),
             (Global "Fin", VLam (\ n -> VFin n)),

             (Global "lteElim", evalChk (Lam (Lam (Lam (Lam (Lam (Lam (Inf (LTEElim (Inf (Bound 5)) (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))))) ([],[])),

             (Global "finElim", evalChk (Lam (Lam (Lam (Lam (Lam (Inf (FinElim (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0))))))))) ([],[]))]
     --       ]

lpassume state@(out, ve, te) x t =
  -- x: String, t: CTerm
  check lp state x (Ann t (Inf Star))
        (\ (y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint_ 0 0 (quote0_ v))))
        (\ (y, v) -> (out, ve, (Global x, v) : te))

lp :: Interpreter TermInf TermChk Value TermChk
lp = I { iname = "lambda-Pi",
         iprompt = "LP> ",
         iitype = \v c -> typeInf 0 (v,c),
         iquote = quote0,
         ieval = \ e x -> evalInf x (e,[]),
         ihastype = id,
         icprint = cPrint_ 0 0,
         itprint = cPrint_ 0 0 . quote0,
         iiparse = parseITerm_ 0 [],
         isparse = parseStmt_ [],
         iassume = \ s (x, t) -> lpassume s x t }

repLP :: IO ()
repLP = readevalprint lp ([], lpve, lpte)

typecheck :: String -> IO State 
typecheck = compileFile lp ([], lpve, lpte)

typecheckandParse :: String -> IO ([Stmt TermInf TermChk], State )
typecheckandParse = compileFileandParse lp ([], lpve, lpte)

renderStmt :: Stmt TermInf TermChk -> String 
renderStmt (Let s t) = "let " ++ s ++ " = " ++ render (iPrint_ 0 0 t)
renderStmt _ = ""

renderStmts :: [Stmt TermInf TermChk] -> String 
renderStmts [] = ""
renderStmts (s : ss) = renderStmt s ++ "\n" ++ renderStmts ss