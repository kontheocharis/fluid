module Syntax2 where

import Syntax

-- Inferrable Terms
data TermInf2 = 
   AnnT TermChk2 TermChk2 Value     -- ANN
 | StarT Value
 | PiT TermChk2 TermChk2 Value      -- Dependent Pi types
 | SigmaT TermChk2 TermChk2 Value   -- Sigma Types
 | BoundT Int Value               -- VAR
 | FreeT Name    Value           -- VAR
 | AppRedT TermInf2 TermChk2 Value     -- APP can be reduced. 
 | AppT TermChk2 TermChk2 Value
 | PairT TermChk2 TermChk2 TermChk2 TermChk2 Value -- Pairs
 | NatT Value 
 | NatElimT TermChk2 TermChk2 TermChk2 TermChk2 Value
 | VecT TermChk2 TermChk2 Value
 | VecElimT TermChk2 TermChk2 TermChk2 TermChk2 TermChk2 TermChk2 Value
 | ListT TermChk2 Value
 | ListElimT TermChk2 TermChk2 TermChk2 TermChk2 TermChk2 Value
 | FinT TermChk2 Value
 | FinElimT TermChk2 TermChk2 TermChk2 TermChk2 TermChk2 Value
 | EqT TermChk2 TermChk2 TermChk2 Value
 | EqElimT TermChk2 TermChk2 TermChk2 TermChk2 TermChk2 TermChk2 Value
 | SigElimT TermChk2 TermChk2 TermChk2 TermChk2 TermChk2 Value
 | TMaybeT TermChk2 Value
 | LTET TermChk2 TermChk2 Value
 | LTEElimT TermChk2 TermChk2 TermChk2 TermChk2 TermChk2 TermChk2 Value

 --     deriving (Show, Eq)

-- Checkable Terms
data TermChk2 =         
   InfT TermInf2 Value         -- CHK
 | LamT TermChk2 Value          -- LAM
 | ZeroT Value
 | SuccT TermChk2 Value
 | NilT TermChk2 Value
 | ConsT TermChk2 TermChk2 TermChk2 TermChk2 Value
 | LNilT TermChk2 Value        -- List Nil
 | LConsT TermChk2 TermChk2 TermChk2 Value-- List Cons
 | VecToListT TermChk2 TermChk2 TermChk2 Value
 | FZeroT TermChk2 Value
 | FSuccT TermChk2 TermChk2 Value
 | ReflT TermChk2 TermChk2 Value
 | TNothingT TermChk2 Value
 | TJustT TermChk2 TermChk2 Value
 | LTEZeroT TermChk2 Value
 | LTESuccT TermChk2 TermChk2 TermChk2 Value

  --    deriving (Show, Eq)



