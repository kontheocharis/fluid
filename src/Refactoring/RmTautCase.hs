module Refactoring.RmTautCase where

import Lang
import Refactoring.Utils
import Refactoring.TraverseUtils
import Interface.Pretty

import Debug.Trace

data RTCArgs = RTCArgs {
  lx :: Int,
  ly :: Int
}

instance FromRefactorArgs RTCArgs where
  fromRefactorArgs as = RTCArgs
    <$> lookupIdxArg "lx" as
    <*> lookupIdxArg "ly" as

rmTautCase :: RTCArgs -> Program -> Refact Program
rmTautCase as p = do
  -- mapTermMappableM f p
  case locToTerm pos p of -- TODO: fix fussiness!
    Nothing -> error "no term at position" 
    Just t ->
      case termToCase pos t p of
        Nothing -> error "Can't find case-expression"
        Just (Term (Case ce cs) td) ->
          error "REST"
          -- determine whether the ce is of the right form
          -- if so replace term w/ True branch of cs
  where
    pos = Pos (lx as) (ly as)
    f tm = trace ("!! " ++ show (getLoc tm, printTerm tm))
         $ return Continue
