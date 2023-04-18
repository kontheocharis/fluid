module Syntax where

-- Inferrable Terms
data TermInf = 
   Ann TermChk TermChk     -- ANN
 | Star
 | Pi TermChk TermChk      -- Dependent Pi types
 | Bound Int               -- VAR
 | Free Name               -- VAR
 | TermInf :@: TermChk     -- APP
 | Nat 
 | NatElim TermChk TermChk TermChk TermChk
 | Vec TermChk TermChk 
 | VecElim TermChk TermChk TermChk TermChk TermChk TermChk
 | Fin TermChk 
 | FinElim TermChk TermChk TermChk TermChk TermChk


      deriving (Show, Eq)

-- Checkable Terms
data TermChk =         
   Inf TermInf          -- CHK
 | Lam TermChk          -- LAM
 | Zero
 | Succ TermChk 
 | Nil TermChk
 | Cons TermChk TermChk TermChk TermChk
 | FZero TermChk
 | FSucc TermChk TermChk

      deriving (Show, Eq)

-- Locally nameless representation
-- Globals are names, locals are De Bruijn representations
-- We can quote functions into this representation
--  to allow for equality checking
data Name = 
   Global String
 | Local Int 
 | Quote Int
       deriving (Show, Eq)

-- Types
-- t := a        base type
--   |  t -> t'  function type

{- 
data Type = 
   TFree Name  
 | Fun Type Type
       deriving (Show, Eq)
-}

-- Terms are evaluated to values
-- v ::= n         neutral term
--       \.x -> v  lambda abstraction
data Value = 
   VNeutral Neutral
 | VLam (Value -> Value)
 | VStar 
 | VPi Value (Value -> Value)
 | VNat 
 | VZero 
 | VSucc Value
 | VNil Value
 | VCons Value Value Value Value
 | VVec Value Value
 | VFZero Value
 | VFSucc Value Value
 | VFin Value


-- n ::= x         variable
--   |   n v       application  
data Neutral = 
   NFree Name 
 | NApp Neutral Value
 | NNatElim Value Value Value Neutral
 | NVecElim Value Value Value Value Value Neutral
 | NFinElim Value Value Value Value Neutral

-- creates a value corrsponding to a free variable
vfree :: Name -> Value
vfree n = VNeutral (NFree n)


