module Main where

-- import Common
import REPL

import Syntax
import Eval
import Typecheck
-- import LambdaPi.Quote
import Parser
import Pretty

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
             (Global "listElim", VPi VStar (\ a ->
                               VPi (VPi (VList a) (\ _ -> VStar)) (\ m ->
                               VPi (m `vapp` (VLNil a)) (\ _ ->
                               VPi (VPi a (\ x ->
                                     VPi (VList a) (\ xs ->
                                     VPi (m `vapp` xs) (\ _ ->
                                     m `vapp` VLCons a x xs)))) (\ _ ->
                               VPi (VList a) (\ xs -> m `vapp` xs)))))),
             (Global "Refl", VPi VStar (\ a -> VPi a (\ x ->
                            VEq a x x))),
             (Global "Eq", VPi VStar (\ a -> VPi a (\ x -> VPi a (\ y -> VStar)))),
             (Global "eqElim", VPi VStar (\ a ->
                              VPi (VPi a (\ x -> VPi a (\ y -> VPi (VEq a x y) (\ _ -> VStar)))) (\ m ->
                              VPi (VPi a (\ x -> ((m `vapp` x) `vapp` x) `vapp` VRefl a x)) (\ _ ->
                              VPi a (\ x -> VPi a (\ y ->
                              VPi (VEq a x y) (\ eq ->
                              ((m `vapp` x) `vapp` y) `vapp` eq))))))),
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
             (Global "Nil", VLam (\ a -> VNil a)),
             (Global "Cons", VLam (\ a -> VLam (\ n -> VLam (\ x -> VLam (\ xs ->
                            VCons a n x xs))))),
             (Global "Vec", VLam (\ a -> VLam (\ n -> VVec a n))),
             (Global "vecElim", evalChk (Lam (Lam (Lam (Lam (Lam (Lam (Inf (VecElim (Inf (Bound 5)) (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))))) ([],[])),
             (Global "Refl", VLam (\ a -> VLam (\ x -> VRefl a x))),
             (Global "Eq", VLam (\ a -> VLam (\ x -> VLam (\ y -> VEq a x y)))),
             (Global "eqElim", evalChk (Lam (Lam (Lam (Lam (Lam (Lam (Inf (EqElim (Inf (Bound 5)) (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))))) ([],[])),
             (Global "FZero", VLam (\ n -> VFZero n)),
             (Global "FSucc", VLam (\ n -> VLam (\ f -> VFSucc n f))),
             (Global "Fin", VLam (\ n -> VFin n)),
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

main :: IO ()
main = repLP