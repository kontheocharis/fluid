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
evalInf Star d = VStar
evalInf (Pi t t') d = VPi (evalChk t d) (\x -> evalChk t' (x:d))
evalInf Nat d = VNat 
evalInf Zero d = VZero 
evalInf (Succ k) d = VSucc (evalChk k d)
evalInf (NatElim m mz ms k) d =
  let mzVal = evalChk mz d
      msVal = evalChk ms d
      rec kVal = 
            case kVal of 
              VZero   -> mzVal 
              VSucc l -> msVal `vapp` l `vapp` rec l -- I don't understand this
              VNeutral k -> VNeutral 
                              (NNatElim (evalChk m d) mzVal msVal k)
              _           -> error "internal: eval natElim"
  in rec (evalChk k d)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v 
vapp (VNeutral n) v = VNeutral (NApp n v)

evalChk :: TermChk -> Env -> Value
evalChk (Inf i) d = evalInf i d
evalChk (Lam e) d = VLam (\x -> evalChk e (x:d))