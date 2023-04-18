module Eval where

import Syntax 

----------------------------------------------------
-- evaluator, big-step
----------------------------------------------------

type Env = [ (Name, Value) ]

evalInf :: TermInf -> (Env, [Value])  -> Value
evalInf (Ann e _) d = evalChk e d
evalInf (Bound i) d = (snd d !! i) 
evalInf (Free x) d  = case lookup x (fst d) of Nothing -> (vfree x); Just v -> v
evalInf (e :@: e') d = vapp (evalInf e d) (evalChk e' d)
evalInf Star d = VStar
evalInf (Pi t t') d = VPi (evalChk t d) (\ x -> evalChk t' (((\(e, d) -> (e,  (x : d))) d)))
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
evalInf (Fin n) d = VFin (evalChk n d)
evalInf (FinElim m mz ms n f) d = 
  let mzVal = evalChk mz d
      msVal = evalChk ms d
      rec fVal = 
        case fVal of 
          VFZero k -> mzVal `vapp` k
          VFSucc k g -> foldl vapp msVal [k,g,rec g]
          VNeutral n' -> VNeutral (NFinElim (evalChk m d) (evalChk mz d)
                                            (evalChk ms d) (evalChk n d) n')

  in rec (evalChk f d)


vapp :: Value -> Value -> Value
vapp (VLam f) v = f v 
vapp (VNeutral n) v = VNeutral (NApp n v)

evalChk :: TermChk -> (Env, [Value]) -> Value
evalChk (Inf i) d = evalInf i d
evalChk (Lam e) d = VLam (\x -> evalChk e (((\(e2, d2) -> (e2,  (x : d2))) d)))
evalChk Zero d = VZero 
evalChk (Succ k) d = VSucc (evalChk k d)
evalChk (Nil a) d = VNil (evalChk a d)
evalChk (Cons a k x xs) d = VCons (evalChk a d) (evalChk k d) (evalChk x d) (evalChk xs d)
evalChk (FZero n) d = VFZero (evalChk n d)
evalChk (FSucc n f) d = VFSucc (evalChk n d) (evalChk f d)

