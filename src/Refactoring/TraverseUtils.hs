module Refactoring.TraverseUtils where

import Refactoring.Utils

import Lang

import GHC.Generics (Generic)
import Data.Generics (Data)
import Data.Typeable (Typeable)
import Generics.SYB hiding (Generic, Refl)

type SimpPos = (Int, Int)

getPos :: Maybe Pos -> Pos 
getPos Nothing = error "Location in source code not found!"
getPos (Just p) = p

locToTerm :: (Data t)
            => Pos 
            -> t
            -> Maybe Term
locToTerm p t = 
   Generics.SYB.something (Nothing `Generics.SYB.mkQ` termBind) t
  where
     termBind term@((Term (V (Var name id)) d)) 
       | getPos (startPos (getLoc d)) == p  = Just term
       | otherwise = Nothing