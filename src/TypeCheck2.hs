module TypeCheck2 where 

import Control.Monad.Except

import Syntax
import Syntax2

import Typecheck
import Eval
import Pretty
import Text.PrettyPrint.HughesPJ hiding (parens)
import Debug.Trace

{-
data Kind = Star
  deriving (Show, Eq)

data Info = 
    HasKind Kind 
  | HasType Type
      deriving (Show)
-}

-- throwError :: String -> Result a 
-- throwError s = Left s 

{-
kindChk :: Context -> Type -> Kind -> Result () 
kindChk env (TFree x) Star 
   = case lookup x env of 
        Just (HasKind Star) -> return () 
        Nothing             -> throwError "unknown identifier"
kindChk env (Fun k k') Star
   = do 
         kindChk env k Star
         kindChk env k' Star
-}

typeInf02 :: ([(Name, Value)], Context) -> TermInf -> Result TermInf2
typeInf02 = typeInf2 0

typeInf2 :: Int -> ([(Name, Value)], Context) -> TermInf -> Result TermInf2
typeInf2 i env a@(Ann e p) 
   = do
        p' <- typeChk2 i env p VStar 
        let t = evalChk p (fst env, [])
        e' <- typeChk2 i env e t
        return (AnnT e' p' t)
typeInf2 i env Star = return (StarT VStar)
typeInf2 i env t1@(Pi p p') 
   = do
         p2 <- typeChk2 i env p VStar
         let t = evalChk p (fst env, []) 
         p'2 <- typeChk2 (i+1) ((\ (d,g) -> (d,  ((Local i, t) : g))) env)  
                        (subsChk 0 (Free (Local i)) p') VStar  
         return (PiT p2 p'2 VStar)
typeInf2 i env (Free x) 
    = case lookup x (snd env) of 
           Just t -> return (FreeT x t )
           Nothing          -> throwError ("unknown identifier " ++ (show x))
typeInf2 i env (e :@: e')
    = do 
         e2 <- typeInf2 i env e 
         case (infToValue e2) of
            VPi t1 t2 -> do e'2 <- typeChk2 i env e' t1
                            return (AppRedT e2 e'2 (t2  (evalChk e' (fst env, []))))
                            
            _        -> throwError "illegal application"
{-
typeInf i env (e :@: e')
    = do 
         s <- typeInf i env e 
         case s of
            VPi t t' -> do typeChk i env e' t
                           return (t'  (evalChk e' (fst env, [])))
            _        -> throwError "illegal application"
-}

typeInf2 i env Nat = return (NatT VStar)
typeInf2 i env (NatElim m mz ms k) = 
   do
      m' <- typeChk2 i env m (VPi VNat (const VStar))
      let mVal = evalChk m (fst env, [])
      mz' <- typeChk2 i env mz (mVal `vapp` VZero)
      ms' <- typeChk2 i env ms (VPi VNat (\l -> VPi (mVal `vapp` l) (\_ -> mVal `vapp` VSucc l)))
      k' <- typeChk2 i env k VNat 
      let kVal = evalChk k (fst env, []) 
      return (NatElimT m' mz' ms' k' (mVal `vapp` kVal))

typeInf2 i env (List a) = 
   do 
      a' <- typeChk2 i env a VStar
      return (ListT a' VStar)

typeInf2 i env (TMaybe a) = 
   do
      a' <- typeChk2 i env a VStar 
      return (TMaybeT a' VStar)

typeInf2 i env (Vec a k) = 
   do
      a' <- typeChk2 i env a VStar 
      k' <- typeChk2 i env k VNat
      return (VecT a' k' VStar)

typeInf2 i env (LTE a b) = 
   do 
      a' <- typeChk2 i env a VNat 
      b' <- typeChk2 i env b VNat 
      return (LTET a' b' VStar)

typeInf2 i env (ListElim a m mn mc vs) =
   do
      a' <- typeChk2 i env a VStar
      let aVal = evalChk a (fst env, [])
      m' <- typeChk2 i env m
         ( VPi (VList aVal) (\_ -> VStar))
      let mVal = evalChk m (fst env, [])
      mn' <- typeChk2 i env mn (foldl vapp mVal [VLNil aVal])
      mc' <- typeChk2 i env mc
         (VPi aVal (\y ->
               VPi (VList aVal) (\ys ->
                  VPi (foldl vapp mVal [ys]) (\_ ->
                     (foldl vapp mVal [VLCons aVal  y ys])))))
      -- typeChk i env k VNat
      -- let kVal = evalChk k (fst env, [])
      vs' <- typeChk2 i env vs (VList aVal)
      let vsVal = evalChk vs (fst env, [])
      error (show $ quote0 vsVal)
      return (ListElimT a' m' mn' mc' vs' (foldl vapp mVal [vsVal]))
      
typeInf2 i env (VecElim a m mn mc k vs) =
   do
      a' <- typeChk2 i env a VStar
      let aVal = evalChk a (fst env, [])
      m' <- typeChk2 i env m
         (VPi VNat (\k -> VPi (VVec aVal k) (\_ -> VStar)))
      let mVal = evalChk m (fst env, [])
      mn' <- typeChk2 i env mn (foldl vapp mVal [VZero, VNil aVal])
      mc' <- typeChk2 i env mc
         (VPi VNat (\l ->
            VPi aVal (\y ->
               VPi (VVec aVal l) (\ys ->
                  VPi (foldl vapp mVal [l,ys]) (\_ ->
                     (foldl vapp mVal [VSucc l, VCons aVal l y ys]))))))
      k' <- typeChk2 i env k VNat
      let kVal = evalChk k (fst env, [])
      vs' <- typeChk2 i env vs (VVec aVal kVal)
      let vsVal = evalChk vs (fst env, [])
      return (VecElimT a' m' mn' mc' k' vs' (foldl vapp mVal [kVal, vsVal]))

 

typeInf2 i env (Fin n) = 
   do n' <- typeChk2 i env n VNat 
      return (FinT n' VStar)

typeInf2 i env (FinElim m mz ms n f) =
   do m' <- typeChk2 i env m (VPi VNat (\k -> VPi (VFin k) (const VStar)))
      let mVal = evalChk m (fst env, [])
      n' <- typeChk2 i env n VNat
      let nVal = evalChk n (fst env, [])
      mz' <- typeChk2 i env mz (VPi VNat (\k -> mVal `vapp` VSucc k `vapp` VFZero k))
      ms' <- typeChk2 i env ms (VPi VNat (\k -> 
          VPi (VFin k) (\fk -> 
              VPi (mVal `vapp` k `vapp` fk) (\_ -> 
                  mVal `vapp` VSucc k `vapp` VFSucc k fk))))
      f' <- typeChk2 i env f (VFin nVal)
      let fVal = evalChk f (fst env, [])
      return (FinElimT m' mz' ms' n' f' (mVal `vapp` nVal `vapp` fVal))
typeInf2 i env (Eq a x y) = 
   do a' <- typeChk2 i env a VStar
      let aVal = evalChk a (fst env, [])
      x' <- typeChk2 i env x aVal 
      y' <- typeChk2 i env y aVal
      return (EqT a' x' y' VStar)
typeInf2 i env (EqElim a m mr x y eq) = 
   do a' <- typeChk2 i env a VStar
      let aVal = evalChk a (fst env, [])
      m' <- typeChk2 i env m 
         (VPi aVal (\x ->
          VPi aVal (\y -> 
          VPi (VEq aVal x y) (\_ -> VStar))))
      let mVal = evalChk m (fst env, []) 
      mr' <- typeChk2 i env mr 
          (VPi aVal (\x -> 
           foldl vapp mVal [x,x,VRefl aVal x]))
      x' <- typeChk2 i env x aVal 
      let xVal = evalChk x (fst env, [])
      y' <- typeChk2 i env y aVal
      let yVal = evalChk y (fst env, [])
      eq' <- typeChk2 i env eq (VEq aVal xVal yVal)
      let eqVal = evalChk eq (fst env, [])
      return (EqElimT a' m' mr' x' y' eq' (foldl vapp mVal [xVal, yVal, eqVal]))

typeInf2 i env (LTEElim x y z a b c) =
  do
      x' <- typeChk2 i env x
         (VPi VNat (\x -> 
           VPi VNat (\y ->
            VPi (VLTE x y) (\_ -> VStar))))
      let xVal = evalChk x (fst env, []) 
      y' <- typeChk2 i env y 
         (VPi VNat (\y -> 
            foldl vapp xVal [VZero, y, (VLTEZero y)]))
      z' <- typeChk2 i env z 
         (VPi VNat (\z -> 
            VPi VNat (\a -> 
             VPi (VLTE z a) (\b -> 
                VPi (foldl vapp xVal [z,a,b]) (\_ ->
                   foldl vapp xVal [VSucc z, VSucc a, VLTESucc z a b])))))
      a' <- typeChk2 i env a VNat 
      let aVal = evalChk a (fst env, [])
      b' <- typeChk2 i env b VNat 
      let bVal = evalChk b (fst env, [])
      c' <- typeChk2 i env c (VLTE aVal bVal)
      let cVal = evalChk c (fst env, [])
      return (LTEElimT x' y' z' a' b' c' (foldl vapp xVal [aVal,bVal,cVal]))
      
         

typeInf2 _ _ tm = throwError $ "No type match for " ++ (show tm) -- render (iPrint_ 0 0 tm)


typeChk2 :: Int -> ([(Name, Value)], Context) -> TermChk -> Value -> Result TermChk2
typeChk2 i env (Inf e) t
   = do 
        e' <- typeInf2 i env e 
        t' <- typeInf i env e
        if ( quote0 t /= quote0 t') 
         then (throwError ("type mismatch:\n" ++ "type inferred:  " 
                    ++ render (cPrint_ 0 0 (quote0 t')) 
                    ++ "\n" 
                    ++ "type expected:  " 
                    ++ render (cPrint_ 0 0 (quote0 t)) 
                    ++ "\n" 
                    ++ "for expression: " 
                    ++ render (iPrint_ 0 0 e) 
                --    ++ "\n\n" 
                --    ++ (show (map (\(x,y) -> (x, (quote0 y))) (snd env))) 
                --    ++ "\n" 
                --    ++ (show (quote0 t')) -- inferred
                --    ++ "\n"  
                --    ++ (show (quote0 t)))) -- expected
         ))
        else return (InfT e' t)
typeChk2 i env t1@(Lam e) (VPi t t') 
   = do
        e' <- typeChk2  (i + 1) ((\ (d,g) -> (d,  ((Local i, t ) : g))) env) (subsChk 0 (Free (Local i)) e) ( t' (vfree (Local i))) 
        return (LamT e' (VPi t t'))

{-
typeChk i env t1@(Pair a b) (VSigma aT bT)
   = do
         typeChk i env a aT
         let atVal = evalChk a (fst env, [])
         typeChk i env b (VPi aT (\x -> VStar)) -- B : A -> Type ?
         -- let bVal = evalChk b (fst env, [])
         -- check b : B(a) 
         typeChk (i + 1) ((\ (d,g) -> (d, ((Local i, atVal) : g))) env) (subsChk 0 (Free (Local i)) b) (bT (vfree (Local i)))
-}

typeChk2 i env Zero VNat = return (ZeroT VNat)
typeChk2 i env (Succ k) VNat = do
                                  k' <- typeChk2 i env k VNat 
                                  return (SuccT k' VNat)

typeChk2 i env (TNothing a) (VMaybe aT) =
  do
      a' <- typeChk2 i env a VStar 
      let aVal = evalChk a (fst env, [])
      if (quote0 aVal /= quote0 aT) then throwError "type mismatch in Nothing and Maybe"
                                    else return ()
      return (TNothingT a' (VMaybe aT))

typeChk2 i env (TJust a b) (VMaybe aT) = 
   do
      a' <- typeChk2 i env a VStar 
      let aVal = evalChk a (fst env, [])
      if (quote0 aVal /= quote0 aT) 
         then throwError "type mismatch in Just and Maybe"
         else do
                  b' <- typeChk2 i env b aVal 
                  return (TJustT a' b' (VMaybe aT))

typeChk2 i env (Nil a) (VVec bVal VZero) = 
   do
      a' <- typeChk2 i env a VStar
      let aVal = evalChk a (fst env, [])
      if (quote0 aVal /= quote0 bVal) then throwError "type mismatch2"
                                      else return (NilT a' (VVec bVal VZero))
      -- return ()
typeChk2 i env (Cons a k x xs) (VVec bVal (VSucc k2)) =
   do
      a' <- typeChk2 i env a VStar
      let aVal = evalChk a (fst env, [])
      if (quote0 aVal /= quote0 bVal) 
            then throwError "type mismatch3"
            else do
               k' <- typeChk2 i env k VNat
               let kVal = evalChk k (fst env, [])
               if (quote0 kVal /= quote0 k2) 
                  then throwError "type mismatch4"
                  else do
                     x' <- typeChk2 i env x aVal
                     xs' <- typeChk2 i env xs (VVec aVal kVal)
                     return (ConsT a' k' x' xs' (VVec bVal (VSucc k2)))
typeChk2 i env (LNil a) (VList bVal) = 
   do
      a' <- typeChk2 i env a VStar
      let aVal = evalChk a (fst env, [])
      if (quote0 aVal /= quote0 bVal) then throwError "type mismatch2"
                                      else return (LNilT a' (VList bVal))
      -- return ()
typeChk2 i env (LCons a x xs) (VList bVal) =
   do
      a' <- typeChk2 i env a VStar
      let aVal = evalChk a (fst env, [])
      if (quote0 aVal /= quote0 bVal) 
            then throwError "type mismatch3"
            else do
               -- typeChk i env k VNat
               -- let kVal = evalChk k (fst env, [])
               -- if (quote0 kVal /= quote0 k2) 
               --   then throwError "type mismatch4"
               --   else do
               x' <- typeChk2 i env x aVal
               xs' <- typeChk2 i env xs (VList aVal)
               return (LConsT a' x' xs' (VList bVal))
typeChk2 i env@(v,t) (FZero n) (VFin (VSucc mVal)) =
 do
    n' <- typeChk2 i env n VNat
    let nVal = evalChk n (v, [])
    if (quote0 nVal /= quote0 mVal) then throwError "number mismatch FZero"
                                    else return (FZeroT n' (VFin (VSucc mVal)))
typeChk2 i env@(v,t) (FSucc n f') (VFin (VSucc mVal)) =
  do
    n' <- typeChk2 i env n VNat
    let nVal = evalChk n (v,[])
    if  (quote0 nVal /= quote0 mVal) then (throwError "number mismatch FSucc")
                                     else do f'' <- typeChk2 i env f' (VFin mVal)
                                             return (FSuccT n' f'' (VFin (VSucc mVal)))
typeChk2 i env@(v,t) (Refl a z) (VEq bVal xVal yVal) =
  do a' <- typeChk2 i env a VStar
     let aVal = evalChk a (fst env, [])
     if (quote0 aVal /= quote0 bVal) 
       then (throwError "type mismatch")
       else do z' <- typeChk2 i env z aVal 
               let zVal = evalChk z (fst env, []) 
               if (quote0 zVal /= quote0 xVal && quote0 zVal /= quote0 yVal) 
                   then (throwError "type mismatch")
                   else return (ReflT a' z' (VEq bVal xVal yVal))
typeChk2 i env@(v,t) (VecToList a n ve) (VList bVal) =
  do a' <- typeChk2 i env a VStar
     let aVal = evalChk a (fst env, [])
     if (quote0 aVal /= quote0 bVal) 
       then (throwError "type mismatch")
       else do n' <- typeChk2 i env n VNat
               let nVal = evalChk n (fst env, [])
               ve' <- typeChk2 i env ve (VVec aVal nVal)
               return (VecToListT a' n' ve' (VList bVal))


typeChk2 i env _ _ = throwError "type mismatch5"

