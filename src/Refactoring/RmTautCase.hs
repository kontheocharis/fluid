module Refactoring.RmTautCase where

import Lang
import Refactoring.Utils
import Refactoring.TraverseUtils
import Interface.Pretty

import Debug.Trace

data RTCArgs = RTCArgs {
  lx :: Int,
  ly :: Int,
  op :: String
}

instance FromRefactorArgs RTCArgs where
  fromRefactorArgs as = RTCArgs
    <$> lookupIdxArg "lx" as
    <*> lookupIdxArg "ly" as
    <*> lookupNameArg "op" as

rmTautCase :: RTCArgs -> Program -> Refact Program
rmTautCase as p = do
  -- mapTermMappableM f p
  case locToTerm' pos p of -- TODO: fix fussiness!
    Nothing -> error $ "no term at position: " ++ show pos
    Just t ->
      case termToCase pos t p of
        Nothing -> error $ "Can't find case-expression containing " ++ show t
        Just (Term c@(Case ce cs) _)
          | length cs == 2 && isAppOf (op as) ce && reflArgs ce ->
            case lookupTrue cs of
              Nothing -> error $ "can't find True branch: " ++ show cs
              Just rhs ->
                replaceTerm c (termValue rhs) p
            -- Bool only so no substitution needed (as no new declarations)
          | otherwise ->
            error $ "unexpected form of case condition: " ++ printTerm 1 ce
        Just e ->
          error $ "Returned something other than a case-expr: " ++ printTerm 1 e
  where
    pos = Pos (lx as) (ly as)
    -- f tm = trace ("!! " ++ show (getLoc tm, printTerm 1 tm))
    --      $ return Continue

isAppOf :: String -> Term -> Bool
isAppOf g (Term (App t1 _) _) = isAppOf' t1 where
  isAppOf' (Term (V (Var f _)) _) | g == f = True
  isAppOf' (Term (Global f) _) | g == f = True
  isAppOf' (Term (App t3 _) _) = isAppOf' t3
  isAppOf' t = trace ("!! " ++ show t) False
isAppOf _ _ = False

reflArgs :: Term -> Bool
reflArgs (Term (App (Term (App _t t2) _) t3) _) = ra t2 t3 where
  ra (Term (V v1) _) (Term (V v2) _) = v1 == v2
  ra _ _ = False
reflArgs e = error $ "unexpected form of case condition: " ++ printTerm 1 e

lookupTrue :: [(Term,Term)] -> Maybe Term
lookupTrue [] = Nothing
lookupTrue ((Term (Global "True") _,rhs) : _) = Just rhs
lookupTrue (_ : cs) = lookupTrue cs
