module Typecheck where 

import Control.Monad.Except

import Syntax
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

type Context = [ (Name, Value) ]

type Result a = Either String a 

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

typeInf0 :: ([(Name, Value)], Context) -> TermInf -> Result Value
typeInf0 = typeInf 0

typeInf :: Int -> ([(Name, Value)], Context) -> TermInf -> Result Value
typeInf i env a@(Ann e p) 
   = do
        typeChk i env p VStar 
        let t = evalChk p (fst env, [])
        typeChk i env e t
        return t
typeInf i env Star = return VStar
typeInf i env t1@(Pi p p') 
   = do
         typeChk i env p VStar
         let t = evalChk p (fst env, []) 
         typeChk (i+1) ((\ (d,g) -> (d,  ((Local i, t) : g))) env)  
                       (subsChk 0 (Free (Local i)) p') VStar  
         return VStar

typeInf i env (Free x) 
    = case lookup x (snd env) of 
           Just t -> return t 
           Nothing          -> throwError ("unknown identifier " ++ (show x))
typeInf i env (e :@: e')
    = do 
         s <- typeInf i env e 
         case s of
            VPi t t' -> do typeChk i env e' t
                           return (t'  (evalChk e' (fst env, [])))
            _        -> throwError "illegal application"
typeInf i env Nat = return VStar
typeInf i env (NatElim m mz ms k) = 
   do
      typeChk i env m (VPi VNat (const VStar))
      let mVal = evalChk m (fst env, [])
      typeChk i env mz (mVal `vapp` VZero)
      typeChk i env ms (VPi VNat (\l -> VPi (mVal `vapp` l) (\_ -> mVal `vapp` VSucc l)))
      typeChk i env k VNat 
      let kVal = evalChk k (fst env, []) 
      return (mVal `vapp` kVal)
typeInf i env (Vec a k) = 
   do
      typeChk i env a VStar 
      typeChk i env k VNat
      return VStar
typeInf i env (VecElim a m mn mc k vs) =
   do
      typeChk i env a VStar
      let aVal = evalChk a (fst env, [])
      typeChk i env m
         (VPi VNat (\k -> VPi (VVec aVal k) (\_ -> VStar)))
      let mVal = evalChk m (fst env, [])
      typeChk i env mn (foldl vapp mVal [VZero, VNil aVal])
      typeChk i env mc
         (VPi VNat (\l ->
            VPi aVal (\y ->
               VPi (VVec aVal l) (\ys ->
                  VPi (foldl vapp mVal [l,ys]) (\_ ->
                     (foldl vapp mVal [VSucc l, VCons aVal l y ys]))))))
      typeChk i env k VNat
      let kVal = evalChk k (fst env, [])
      typeChk i env vs (VVec aVal kVal)
      let vsVal = evalChk vs (fst env, [])
      return (foldl vapp mVal [kVal, vsVal])
typeInf _ _ tm = throwError $ "No type match for " ++ (show tm) -- render (iPrint_ 0 0 tm)


typeChk :: Int -> ([(Name, Value)], Context) -> TermChk -> Value -> Result ()
typeChk i env (Inf e) t
   = do 
        t' <- typeInf i env e 
        unless ( quote0 t == quote0 t') (throwError ("type mismatch:\n" ++ "type inferred:  " ++ render (cPrint_ 0 0 (quote0 t')) ++ "\n" ++ "type expected:  " ++ render (cPrint_ 0 0 (quote0 t)) ++ "\n" ++ "for expression: " ++ render (iPrint_ 0 0 e) ++ " " ++ (show (map (\(x,y) -> (x, (quote0 y))) (snd env)))))
typeChk i env t1@(Lam e) (VPi t t') 
   = typeChk  (i + 1) ((\ (d,g) -> (d,  ((Local i, t ) : g))) env) (subsChk 0 (Free (Local i)) e) ( t' (vfree (Local i))) 
typeChk i env Zero VNat = return ()
typeChk i env (Succ k) VNat = typeChk i env k VNat 
typeChk i env (Nil a) (VVec bVal VZero) = 
   do
      typeChk i env a VStar
      let aVal = evalChk a (fst env, [])
      if (quote0 aVal /= quote0 bVal) then throwError "type mismatch2"
                                      else return ()
      return ()
typeChk i env (Cons a k x xs) (VVec bVal (VSucc k2)) =
   do
      typeChk i env a VStar
      let aVal = evalChk a (fst env, [])
      if (quote0 aVal /= quote0 bVal) 
            then throwError "type mismatch3"
            else do
               typeChk i env k VNat
               let kVal = evalChk k (fst env, [])
               if (quote0 kVal /= quote0 k2) 
                  then throwError "type mismatch4"
                  else do
                     typeChk i env x aVal
                     typeChk i env xs (VVec aVal kVal)
                     return ()


typeChk i env _ _ = throwError "type mismatch5"

subsInf :: Int -> TermInf -> TermInf -> TermInf 
subsInf i r (Ann e t) = Ann (subsChk i r e) (subsChk i r t)
subsInf i r (Bound j) = if i == j then r else Bound j
subsInf i r (Free y) = Free y 
subsInf i r (e :@: e') = subsInf i r e :@: subsChk i r e'
subsInf i r Star      = Star
subsInf i r (Pi t t') = Pi (subsChk i r t) (subsChk (i + 1) r t') 
subsInf i r Nat = Nat 
subsInf i r (NatElim m mz ms n) = 
               NatElim (subsChk i r m) (subsChk i r mz)
                       (subsChk i r ms) (subsChk i r n)
subsInf i r (Vec a n) = Vec (subsChk i r a) (subsChk i r n)
subsInf i r (VecElim a m mn mc n xs) = 
                VecElim (subsChk i r a) (subsChk i r m)
                        (subsChk i r mn) (subsChk i r mc)
                        (subsChk i r n)  (subsChk i r xs)

subsChk :: Int -> TermInf -> TermChk -> TermChk 
subsChk i r (Inf e) = Inf (subsInf i r e) 
subsChk i r (Lam e) = Lam (subsChk (i+1) r e)
subsChk i r Zero  = Zero
subsChk i r (Succ n) = Succ (subsChk i r n)
subsChk i r (Nil a) = Nil (subsChk i r a)
subsChk i r (Cons a n x xs) = 
         Cons (subsChk i r a) (subsChk i r n)
              (subsChk i r x) (subsChk i r xs)

quote0 :: Value -> TermChk
quote0 = quote 0 

quote :: Int -> Value -> TermChk
quote i (VNeutral n) = Inf (neutralQuote i n)
quote i (VLam f)     = Lam (quote (i+1) (f (vfree (Quote i))))
quote i (VStar)      = Inf Star
quote i (VPi v f)
  = Inf (Pi (quote i v) (quote (i+1) (f (vfree (Quote i)))))
quote i (VNat) = Inf Nat
quote i VZero = Zero
quote i (VSucc n) = Succ (quote i n)
quote i (VNil a) = Nil (quote i a)
quote i (VCons a n x xs) = Cons (quote i a) (quote i n) (quote i x) (quote i xs)
quote i (VVec a n) = Inf (Vec (quote i a) (quote i n))

neutralQuote :: Int -> Neutral -> TermInf
neutralQuote i (NFree x) = boundFree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v
neutralQuote i (NNatElim m z s n) = NatElim (quote i m) (quote i z) (quote i s) (Inf (neutralQuote i n))
neutralQuote i (NVecElim a m mn mc n xs) =
         VecElim (quote i a) (quote i m)
                 (quote i mn) (quote i mc)
                 (quote i n) (Inf (neutralQuote i xs))

boundFree :: Int -> Name -> TermInf 
boundFree i (Quote k) = Bound (i-k-1)
boundFree i x = Free x