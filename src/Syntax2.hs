module Syntax2 where

import Text.PrettyPrint.HughesPJ hiding (parens)
import Text.ParserCombinators.Parsec.Pos       


import Syntax
import Pretty

import Typecheck


renderVal :: Value -> String 
renderVal v = " (" ++ show (quote0 v) ++ " )"

-- Inferrable Terms
data TermInf2 = 
   AnnT TermChk2 TermChk2 Value     -- ANN
 | StarT Value
 | PiT TermChk2 TermChk2 Value      -- Dependent Pi types
 | SigmaT TermChk2 TermChk2 Value   -- Sigma Types
 | BoundT SourcePos Int Value               -- VAR
 | FreeT SourcePos Name    Value           -- VAR
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

infToValue :: TermInf2 -> Value 
infToValue (AnnT _ _ v) = v 
infToValue (StarT v) = v
infToValue (PiT _ _ v) = v 
infToValue (SigmaT _ _ v) = v
infToValue (BoundT _ _ v) = v 
infToValue (FreeT _ _ v) = v 
infToValue (AppRedT _ _ v) = v
infToValue (AppT _ _ v) = v 
infToValue (PairT _ _ _ _ v) = v 
infToValue (NatT v) = v 
infToValue (NatElimT _ _ _ _ v) = v 
infToValue (VecT _ _ v) = v
infToValue (VecElimT _ _ _ _ _ _ v) = v 
infToValue (ListT _ v) = v 
infToValue (ListElimT _ _ _ _ _ v) = v 
infToValue (FinT _ v) = v
infToValue (FinElimT _ _ _ _ _ v) = v
infToValue (EqT _ _ _ v) = v 
infToValue (EqElimT _ _ _ _ _ _ v) = v 
infToValue (SigElimT _ _ _ _ _ v) = v 
infToValue (TMaybeT _ v) = v
infToValue (LTET _ _ v) = v 
infToValue (LTEElimT _ _ _ _ _ _ v) = v 


renderInf :: TermInf2 -> String 
renderInf (AnnT t1 t2 v) = "(AnnT " ++ renderChk t1 ++ renderChk t2 ++ renderVal v ++")"
renderInf (StarT v) = "(StarT " ++ renderVal v ++")"
renderInf (PiT t1 t2 v) = "(PiT " ++ renderChk t1 ++ renderChk t2 ++ renderVal v ++")"
renderInf (SigmaT t1 t2 v) = "(SigmaT " ++ renderChk t1 ++ renderChk t2 ++ renderVal v ++")"
renderInf (BoundT s i v) = "(BoundT " ++ show s ++ show i ++ renderVal v  ++")"
renderInf (FreeT s n v) = "(FreeT " ++ show s ++ "("++show n++")" ++ renderVal v  ++")"
renderInf (AppRedT ti tc v) = "(AppRedT " ++ renderInf ti ++ renderChk tc ++ renderVal v  ++")"
renderInf (AppT t1 t2 v) = "(AppT " ++ renderChk t1 ++ renderChk t2 ++ renderVal v ++")"
renderInf (PairT t1 t2 t3 t4 v) = "(PairT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderChk t4 ++ renderVal v ++")"
renderInf (NatT v) = "(NatT " ++ renderVal v  ++")"
renderInf (NatElimT t1 t2 t3 t4 v) = "(NatElimT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderChk t4 ++ renderVal v ++")"
renderInf (VecT t1 t2 v) = "(VecT " ++ renderChk t1 ++ renderChk t2 ++ renderVal v ++")"
renderInf (VecElimT t1 t2 t3 t4 t5 t6 v) = "(VecElimT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderChk t4 
                                                       ++ renderChk t5 ++ renderChk t6 ++ renderVal v ++")"
renderInf (ListT t v) = "(ListT " ++ renderChk t ++ renderVal v ++")"
renderInf (ListElimT t1 t2 t3 t4 t5 v) = "(ListElimT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderChk t4 
                                                       ++ renderChk t5 ++ renderVal v ++")"
renderInf (FinT t v) = "(FinT " ++ renderChk t ++ renderVal v ++")"
renderInf (FinElimT t1 t2 t3 t4 t5 v) = "(FinElimT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderChk t4 
                                                    ++ renderChk t5 ++ renderVal v ++")"
renderInf (EqT t1 t2 t3 v) = "(EqT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderVal v ++")"
renderInf (EqElimT t1 t2 t3 t4 t5 t6 v) = "(EqElimT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderChk t4 
                                                     ++ renderChk t5 ++ renderChk t6 ++ renderVal v ++")"
renderInf (SigElimT t1 t2 t3 t4 t5 v) = "(SigElimT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderChk t4
                                                    ++ renderChk t5 ++ renderVal v ++")"
renderInf (TMaybeT t v) = "(TMaybeT " ++ renderChk t ++ renderVal v ++")" 
renderInf (LTET t1 t2 v) = "(LTET " ++ renderChk t1 ++ renderChk t2 ++ renderVal v ++")"
renderInf (LTEElimT t1 t2 t3 t4 t5 t6 v) = "(LTEElimT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderChk t4 
                                                       ++ renderChk t5 ++ renderChk t6 ++ renderVal v ++")"
 --     deriving (Show, Eq)

termInf2ToTermInf :: TermInf2 -> TermInf
termInf2ToTermInf (AnnT t1 t2 v) = Ann (termChk2ToTermChk t1) (termChk2ToTermChk t2)
termInf2ToTermInf (StarT v) = Star
termInf2ToTermInf (PiT t1 t2 v) = Pi (termChk2ToTermChk t1) (termChk2ToTermChk t2)
termInf2ToTermInf (SigmaT t1 t2 v) = Sigma (termChk2ToTermChk t1) (termChk2ToTermChk t2)
termInf2ToTermInf (BoundT s i v) = Bound s i 
termInf2ToTermInf (FreeT s n v) = Free s n
termInf2ToTermInf (AppRedT ti tc v) = (termInf2ToTermInf ti) :@: (termChk2ToTermChk tc)
termInf2ToTermInf (AppT t1 t2 v) = App (termChk2ToTermChk t1) (termChk2ToTermChk t2)
termInf2ToTermInf (PairT t1 t2 t3 t4 v) = Pair (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3) (termChk2ToTermChk t4)
termInf2ToTermInf (NatElimT t1 t2 t3 t4 v) = NatElim (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3) (termChk2ToTermChk t4)
termInf2ToTermInf (VecT t1 t2 v) = Vec (termChk2ToTermChk t1) (termChk2ToTermChk t2)
termInf2ToTermInf (VecElimT t1 t2 t3 t4 t5 t6 v) = VecElim (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3) (termChk2ToTermChk t4)  (termChk2ToTermChk t5) (termChk2ToTermChk t6)
termInf2ToTermInf (ListT t v) = List (termChk2ToTermChk t)
termInf2ToTermInf (ListElimT t1 t2 t3 t4 t5 v) = ListElim (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3) (termChk2ToTermChk t4)  (termChk2ToTermChk t5)
termInf2ToTermInf (FinT t v) = Fin (termChk2ToTermChk t)
termInf2ToTermInf (FinElimT t1 t2 t3 t4 t5 v) = FinElim (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3) (termChk2ToTermChk t4)  (termChk2ToTermChk t5)
termInf2ToTermInf (EqT t1 t2 t3 v) = Eq (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3)
termInf2ToTermInf (EqElimT t1 t2 t3 t4 t5 t6 v) = EqElim (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3) (termChk2ToTermChk t4)  (termChk2ToTermChk t5) (termChk2ToTermChk t6)
termInf2ToTermInf (SigElimT t1 t2 t3 t4 t5 v) = SigElim (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3) (termChk2ToTermChk t4)  (termChk2ToTermChk t5)
termInf2ToTermInf (TMaybeT t v) = TMaybe (termChk2ToTermChk t)
termInf2ToTermInf (LTET t1 t2 v) = LTE (termChk2ToTermChk t1) (termChk2ToTermChk t2)
termInf2ToTermInf (LTEElimT t1 t2 t3 t4 t5 t6 v) = LTEElim (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3) (termChk2ToTermChk t4)  (termChk2ToTermChk t5) (termChk2ToTermChk t6)

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

renderChk :: TermChk2 -> String 
renderChk (InfT t v) = "(InfT " ++ renderInf t ++ renderVal v ++ ")"
renderChk (LamT t v) = "(LamT " ++ renderChk t ++ renderVal v ++ ")"
renderChk (ZeroT v) = "(ZeroT " ++ renderVal v  ++ ")"
renderChk (SuccT t v) = "(SuccT " ++ renderChk t ++ renderVal v  ++ ")"
renderChk (NilT t v) = "(NilT " ++ renderChk t ++ renderVal v  ++ ")"
renderChk (ConsT t1 t2 t3 t4 v) = "(ConsT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderChk t4 ++ renderVal v  ++ ")"
renderChk (LNilT t v) = "(LNilT " ++ renderChk t ++ renderVal v  ++ ")"
renderChk (LConsT t1 t2 t3 v) = "(LConsT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderVal v  ++ ")"
renderChk (VecToListT t1 t2 t3 v) = "(VecToListT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderVal v  ++ ")"
renderChk (FZeroT t v) = "(FZeroT " ++ renderChk t ++ renderVal v  ++ ")"
renderChk (FSuccT t1 t2 v) = "(FSuccT " ++ renderChk t1 ++ renderChk t2 ++ renderVal v  ++ ")"
renderChk (ReflT t1 t2 v) = "(ReflT " ++ renderChk t1 ++ renderChk t2 ++ renderVal v  ++ ")"
renderChk (TNothingT t v) = "(TNothingT " ++ renderChk t ++ renderVal v  ++ ")"
renderChk (TJustT t1 t2 v) = "(TJustT " ++ renderChk t1 ++ renderChk t2 ++ renderVal v  ++ ")"
renderChk (LTEZeroT t v) = "(LTEZeroT " ++ renderChk t ++ renderVal v  ++ ")"
renderChk (LTESuccT t1 t2 t3 v) = "(LTESuccT " ++ renderChk t1 ++ renderChk t2 ++ renderChk t3 ++ renderVal v  ++ ")"

  --    deriving (Show, Eq)

termChk2ToTermChk :: TermChk2 -> TermChk
termChk2ToTermChk (InfT t v) = Inf (termInf2ToTermInf t)
termChk2ToTermChk (LamT t v) = Lam (termChk2ToTermChk t)
termChk2ToTermChk (ZeroT v) = Zero
termChk2ToTermChk (SuccT t v) = Succ (termChk2ToTermChk t)
termChk2ToTermChk (NilT t v) = Nil (termChk2ToTermChk t)
termChk2ToTermChk (ConsT t1 t2 t3 t4 v) = Cons (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3) (termChk2ToTermChk t4) 
termChk2ToTermChk (LNilT t v) = LNil (termChk2ToTermChk t)
termChk2ToTermChk (LConsT t1 t2 t3 v) = LCons (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3)
termChk2ToTermChk (VecToListT t1 t2 t3 v) = VecToList (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3)
termChk2ToTermChk (FZeroT t v) = FZero (termChk2ToTermChk t)
termChk2ToTermChk (FSuccT t1 t2 v) = FSucc (termChk2ToTermChk t1) (termChk2ToTermChk t2)
termChk2ToTermChk (ReflT t1 t2 v) = Refl (termChk2ToTermChk t1) (termChk2ToTermChk t2)
termChk2ToTermChk (TNothingT t v) = TNothing (termChk2ToTermChk t)
termChk2ToTermChk (TJustT t1 t2 v) = TJust (termChk2ToTermChk t1) (termChk2ToTermChk t2)
termChk2ToTermChk (LTEZeroT t v) = LTEZero (termChk2ToTermChk t)
termChk2ToTermChk (LTESuccT t1 t2 t3 v) = LTESucc (termChk2ToTermChk t1) (termChk2ToTermChk t2) (termChk2ToTermChk t3)