module Refactoring.TraverseUtils where

import Refactoring.Utils

import Lang

import GHC.Generics (Generic)
import Data.Generics (Data)
import Data.Typeable (Typeable)
import Generics.SYB hiding (Generic, Refl)

type SimpPos = (Int, Int)

locToTerm :: (Data t)
            => Pos 
            -> t
            -> Maybe Term
locToTerm p t = 
   Generics.SYB.something (Nothing `Generics.SYB.mkQ` termBind) t
  where
     termBind term@((Term (V (Var name id)) d)) 
       | Just p == startPos (getLoc d)    = Just term 
       | otherwise = Nothing
     termBind _ = Nothing 

-- Find the declaring clause for a term
termToClause :: (Data t)
            => Term 
            -> t 
            -> Maybe Clause
termToClause (Term t d) prog = 
    Generics.SYB.something (Nothing `Generics.SYB.mkQ` inClause) prog 
   where
    inClause (Clause pats te (Loc start end))
      | getLinePos (startPos (getLoc d)) >= getLinePos (Just start) && 
        getColPos (startPos (getLoc d)) >= getColPos (Just start) &&
        getLinePos (endPos (getLoc d)) <= getLinePos (Just end) &&
        getColPos (endPos (getLoc d)) <= getLinePos (Just end) = Just $ Clause pats te (Loc start end)
    inClause _ = Nothing
