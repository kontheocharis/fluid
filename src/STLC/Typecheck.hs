module Typecheck where 

import Syntax

data Kind = Star
  deriving (Show, Eq)

data Info = 
    HasKind Kind 
  | HasType Type
      deriving (Show)

type Context = [ (Name, Info) ]

type Result a = Either String a 

throwError :: String -> Result a 
throwError s = Left s 

kindChk :: Context -> Type -> Kind -> Result () 
kindChk env (TFree x) Star 
   = case lookup x env of 
        Just (HasKind Star) -> return () 
        Nothing             -> throwError "unknown identifier"
kindChk env (Fun k k') Star
   = do 
         kindChk env k Star
         kindChk env k' Star

typeInf0 :: Context -> TermInf -> Result Type
typeInf0 = typeInf 0

typeInf :: Int -> Context -> TermInf -> Result Type 
typeInf i env (Ann e t) 
   = do
        kindChk env t Star 
        typeChk i env e t
        return t
typeInf i env (Free x) 
    = case lookup x env of 
           Just (HasType t) -> return t 
           Nothing          -> throwError "unknown identifier"
typeInf i env (e :@: e')
    = do 
         s <- typeInf i env e 
         case s of
            Fun t t' -> do typeChk i env e' t
                           return t' 
            _        -> throwError "illegal application"

typeChk :: Int -> Context -> TermChk -> Type -> Result ()
typeChk i env (Inf e) t
   = do 
        t' <- typeInf i env e 
        if (t == t') then return () else throwError "type mismatch"
typeChk i env (Lam e) (Fun t t') 
   = typeChk (i+1) ((Local i, HasType t):env) (subsChk 0 (Free (Local i)) e) t'
typeChk i env _ _ = throwError "type mismatch"

subsInf :: Int -> TermInf -> TermInf -> TermInf 
subsInf i r (Ann e t) = Ann (subsChk i r e) t
subsInf i r (Bound j) = if i == j then r else Bound j
subsInf i r (Free y) = Free y 
subsInf i r (e :@: e') = subsInf i r e :@: subsChk i r e'

subsChk :: Int -> TermInf -> TermChk -> TermChk 
subsChk i r (Inf e) = Inf (subsInf i r e) 
subsChk i r (Lam e) = Lam (subsChk (i+1) r e)

quote0 :: Value -> TermChk
quote0 = quote 0 

quote :: Int -> Value -> TermChk
quote i (VNeutral n) = Inf (neutralQuote i n)
quote i (VLam f)     = Lam (quote (i+1) (f (vfree (Quote i))))

neutralQuote :: Int -> Neutral -> TermInf
neutralQuote i (NFree x) = boundFree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundFree :: Int -> Name -> TermInf 
boundFree i (Quote k) = Bound (i-k-1)
boundFree i x = Free x