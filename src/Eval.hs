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
evalInf (List a) d = VList (evalChk a d)
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
evalInf (ListElim a mn mc xs) d = 
    let mnVal = evalChk mn d
        mcVal = evalChk mc d
        rec xsVal = 
           case xsVal of
             VLNil _ -> mnVal 
             VLCons _ x xs -> foldl lapp mcVal [x,xs,rec xs]
             VNeutral n -> VNeutral (NListElim (evalChk a d) mnVal mcVal n)
             _ -> error "internal: eval listElim"
        in rec (evalChk xs d)
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
evalInf (Eq a x y) d = VEq (evalChk a d) (evalChk x d) (evalChk y d)
evalInf (EqElim a m mr x y eq) d = 
  let mrVal = evalChk mr d 
      rec eqVal = 
        case eqVal of 
          VRefl _ z -> mrVal `vapp` z
          VNeutral n-> VNeutral (NEqElim (evalChk a d) (evalChk m d) mrVal (evalChk x d) (evalChk y d) n)
          _ -> error "internal: eval eqElim"
  in rec (evalChk eq d)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v 
vapp (VNeutral n) v = VNeutral (NApp n v)

lapp :: Value -> Value -> Value
lapp (VLam f) v = f v 
lapp (VNeutral n) v = VNeutral (NApp n v)


evalChk :: TermChk -> (Env, [Value]) -> Value
evalChk (Inf i) d = evalInf i d
evalChk (Lam e) d = VLam (\x -> evalChk e (((\(e2, d2) -> (e2,  (x : d2))) d)))
evalChk Zero d = VZero 
evalChk (Succ k) d = VSucc (evalChk k d)
evalChk (Nil a) d = VNil (evalChk a d)
evalChk (Cons a k x xs) d = VCons (evalChk a d) (evalChk k d) (evalChk x d) (evalChk xs d)
evalChk (LNil a) d = VLNil (evalChk a d)
evalChk (LCons a x xs) d = VLCons (evalChk a d) (evalChk x d) (evalChk xs d)
evalChk (FZero n) d = VFZero (evalChk n d)
evalChk (FSucc n f) d = VFSucc (evalChk n d) (evalChk f d)
evalChk (Refl a x) d = VRefl (evalChk a d) (evalChk x d)
