module Eval where

import Syntax 

----------------------------------------------------
-- evaluator, big-step
----------------------------------------------------

type Env = [ Value ]

evalInf :: TermInf -> Env -> Value
evalInf (Ann e _) d = evalChk e d
evalInf (Bound i) d = d !! i 
evalInf (Free x) d  = vfree x
evalInf (e :@: e') d = vapp (evalInf e d) (evalChk e' d)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v 
vapp (VNeutral n) v = VNeutral (NApp n v)

evalChk :: TermChk -> Env -> Value
evalChk (Inf i) d = evalInf i d
evalChk (Lam e) d = VLam (\x -> evalChk e (x:d))