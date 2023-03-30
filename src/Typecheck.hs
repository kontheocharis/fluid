module Typecheck where 

import Syntax
import Eval

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

throwError :: String -> Result a 
throwError s = Left s 

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

typeInf0 :: Context -> TermInf -> Result Value
typeInf0 = typeInf 0

typeInf :: Int -> Context -> TermInf -> Result Value
typeInf i env (Ann e p) 
   = do
        typeChk i env p VStar 
        let t = evalChk p []
        typeChk i env e t
        return t
typeInf i env Star = return VStar
typeInf i env (Pi p p') 
   = do
         typeChk i env p VStar
         let t = evalChk p [] 
         typeChk (i+1) ((Local i, t) : env)
                       (subsChk 0 (Free (Local i)) p') VStar
         return VStar

typeInf i env (Free x) 
    = case lookup x env of 
           Just t -> return t 
           Nothing          -> throwError "unknown identifier"
typeInf i env (e :@: e')
    = do 
         s <- typeInf i env e 
         case s of
            VPi t t' -> do typeChk i env e' t
                           return (t'  (evalChk e' []))
            _        -> throwError "illegal application"

typeChk :: Int -> Context -> TermChk -> Value -> Result ()
typeChk i env (Inf e) t
   = do 
        t' <- typeInf i env e 
        if (quote0 t == quote0 t') then return () else throwError "type mismatch"
typeChk i env (Lam e) (VPi t t') 
   = typeChk (i+1) ((Local i, t):env) (subsChk 0 (Free (Local i)) e) (t' (vfree (Local i)))
typeChk i env _ _ = throwError "type mismatch"

subsInf :: Int -> TermInf -> TermInf -> TermInf 
subsInf i r (Ann e t) = Ann (subsChk i r e) t
subsInf i r (Bound j) = if i == j then r else Bound j
subsInf i r (Free y) = Free y 
subsInf i r (e :@: e') = subsInf i r e :@: subsChk i r e'
subsInf i r Star      = Star
subsInf i r (Pi t t') = Pi (subsChk i r t) (subsChk (i + 1) r t') 

subsChk :: Int -> TermInf -> TermChk -> TermChk 
subsChk i r (Inf e) = Inf (subsInf i r e) 
subsChk i r (Lam e) = Lam (subsChk (i+1) r e)

quote0 :: Value -> TermChk
quote0 = quote 0 

quote :: Int -> Value -> TermChk
quote i (VNeutral n) = Inf (neutralQuote i n)
quote i (VLam f)     = Lam (quote (i+1) (f (vfree (Quote i))))
quote i (VStar)      = Inf Star
quote i (VPi v f)
  = Inf (Pi (quote i v) (quote (i+1) (f (vfree (Quote i)))))

neutralQuote :: Int -> Neutral -> TermInf
neutralQuote i (NFree x) = boundFree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundFree :: Int -> Name -> TermInf 
boundFree i (Quote k) = Bound (i-k-1)
boundFree i x = Free x