module Syntax where

-- Inferrable Terms
data TermInf = 
   Ann TermChk Type 
 | Bound Int 
 | Free Name 
 | TermInf :@: TermChk
      deriving (Show, Eq)

