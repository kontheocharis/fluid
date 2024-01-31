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