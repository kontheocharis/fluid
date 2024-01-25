module Parsing.Resolution (resolveGlobalsRec) where

import Checking.Context (GlobalCtx, lookupItemOrCtor)
import Lang
  ( MapResult (Continue, Replace),
    Term (..),
    TermValue (..),
    Var (..),
  )

-- | Resolve global variables in a term.
resolveGlobalsRec :: GlobalCtx -> Term -> MapResult Term
resolveGlobalsRec ctx (Term (V (Var v _)) d) = case lookupItemOrCtor v ctx of
  Just _ -> Replace (Term (Global v) d)
  Nothing -> Continue
resolveGlobalsRec _ _ = Continue
