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
evalInf (Vec a n) d = VVec (evalChk a d) (evalChk n d)
evalInf (VecElim a m mn mc k xs) d = 
    let mnVal = evalChk mn d
        mcVal = evalChk mc d
        rec kVal xsVal = 
           case xsVal of
             VNil _ -> mnVal 
             VCons _ l x xs -> foldl vapp mcVal [l,x,xs,rec l xs]
             VNeutral n -> VNeutral (NVecElim (evalChk a d) (evalChk m d) 
                                               mnVal mcVal kVal n)
             _ -> error "internal: eval vecElim"
        in rec (evalChk k d) (evalChk xs d)



vapp :: Value -> Value -> Value
vapp (VLam f) v = f v 
vapp (VNeutral n) v = VNeutral (NApp n v)

evalChk :: TermChk -> Env -> Value
evalChk (Inf i) d = evalInf i d
evalChk (Lam e) d = VLam (\x -> evalChk e (x:d))
evalChk Zero d = VZero 
evalChk (Succ k) d = VSucc (evalChk k d)
evalChk (Nil a) d = VNil (evalChk a d)
evalChk (Cons a k x xs) d = VCons (evalChk a d) (evalChk k d) (evalChk x d) (evalChk xs d)
