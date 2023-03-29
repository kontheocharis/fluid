module Syntax where

-- Inferrable Terms
data TermInf = 
   Ann TermChk Type     -- ANN
 | Bound Int            -- VAR
 | Free Name            -- VAR
 | TermInf :@: TermChk  -- APP
      deriving (Show, Eq)

-- Checkable Terms
data TermChk =         
   Inf TermInf          -- CHK
 | Lam TermChk          -- LAM
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
data Type = 
   TFree Name  
 | Fun Type Type
       deriving (Show, Eq)

-- Terms are evaluated to values
-- v ::= n         neutral term
--       \.x -> v  lambda abstraction
data Value = 
   VNeutral Neutral
 | VLam (Value -> Value)

-- n ::= x         variable
--   |   n v       application  
data Neutral = 
   NFree Name 
 | NApp Neutral Value

-- creates a value corrsponding to a free variable
vfree :: Name -> Value
vfree n = VNeutral (NFree n)


