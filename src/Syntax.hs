module Syntax where

-- Inferrable Terms
data TermInf = 
   Ann TermChk TermChk     -- ANN
 | Star
 | Pi TermChk TermChk      -- Dependent Pi types
 | Sigma TermChk TermChk   -- Sigma Types
 | Bound Int               -- VAR
 | Free Name               -- VAR
 | TermInf :@: TermChk     -- APP can be reduced. 
 | App TermChk TermChk
 | Pair TermChk TermChk TermChk TermChk -- Pairs
 | Nat 
 | NatElim TermChk TermChk TermChk TermChk
 | Vec TermChk TermChk 
 | VecElim TermChk TermChk TermChk TermChk TermChk TermChk
 | List TermChk
 | ListElim TermChk TermChk TermChk TermChk TermChk 
 | Fin TermChk 
 | FinElim TermChk TermChk TermChk TermChk TermChk
 | Eq TermChk TermChk TermChk
 | EqElim TermChk TermChk TermChk TermChk TermChk TermChk
 | SigElim TermChk TermChk TermChk TermChk TermChk
 | TMaybe TermChk


      deriving (Show, Eq)

-- Checkable Terms
data TermChk =         
   Inf TermInf          -- CHK
 | Lam TermChk          -- LAM
 | Zero
 | Succ TermChk 
 | Nil TermChk
 | Cons TermChk TermChk TermChk TermChk
 | LNil TermChk         -- List Nil
 | LCons TermChk TermChk TermChk -- List Cons
 | VecToList TermChk TermChk TermChk
 | FZero TermChk
 | FSucc TermChk TermChk
 | Refl TermChk TermChk
 | TNothing TermChk
 | TJust TermChk TermChk

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
 | VSigma Value Value -- (Value -> Value)
 | VPair Value Value Value Value
 | VApp Value Value 
 | VNat 
 | VZero 
 | VSucc Value
 | VNil Value
 | VCons Value Value Value Value
 | VVec Value Value
 | VList Value
 | VLNil Value 
 | VLCons Value Value Value 
 | VFZero Value
 | VFSucc Value Value
 | VFin Value
 | VRefl Value Value
 | VEq Value Value Value
 | VMaybe Value 
 | VNothing Value 
 | VJust Value Value 


-- n ::= x         variable
--   |   n v       application  
data Neutral = 
   NFree Name 
 | NApp Neutral Value
 | NNatElim Value Value Value Neutral
 | NVecElim Value Value Value Value Value Neutral
 | NListElim Value Value Value Value Neutral
 | NFinElim Value Value Value Value Neutral
 | NEqElim Value Value Value Value Value Neutral
 | NVecToList Value Neutral

-- creates a value corrsponding to a free variable
vfree :: Name -> Value
vfree n = VNeutral (NFree n)


