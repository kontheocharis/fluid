module Checking.Vars (var, Sub (..), Subst, sub, subVar, alphaRename, noSub) where

import Data.List (intercalate)
import Lang

-- | Helper function to create a variable without caring about the unique identifier.
var :: String -> Var
var x = Var x 0

-- | A substitution, represented as a list of variable-term pairs.
newtype Sub = Sub [(Var, Term)]

instance Show Sub where
  show (Sub s) = "[" ++ intercalate ", " (map (\(v, t) -> show v ++ " -> " ++ show t) s) ++ "]"

-- | Empty substitution.
noSub :: Sub
noSub = Sub []

instance Monoid Sub where
  mempty = noSub

instance Semigroup Sub where
  -- This is not a particularly smart way to do this, but it works.
  (<>) (Sub s1) (Sub s2) = Sub (as ++ bs)
    where
      Sub as = sub (Sub s1) (Sub s2)
      Sub bs = sub (Sub s2) (Sub s1)

-- | A typeclass for things that can be substituted.
class Subst a where
  -- | Apply a `Sub` to a term.
  sub :: Sub -> a -> a
  sub (Sub ((v, t') : ss)) t = sub (Sub ss) (subVar v t' t)
  sub (Sub []) t = t

  -- | Substitute a variable for a term in a term.
  subVar :: Var -> Term -> a -> a

instance Subst Term where
  subVar v t' =
    mapTerm
      ( \t'' -> case t'' of
          V v' | v == v' -> Just t'
          Hole v' | v == v' -> Just t'
          _ -> Nothing
      )

instance Subst Sub where
  subVar v' t' (Sub ((v, t) : s)) = Sub ((v, subVar v' t' t) : let Sub rs = subVar v' t' (Sub s) in rs)
  subVar _ _ (Sub []) = Sub []

-- | Alpha rename a variable in a term.
alphaRename :: Var -> Var -> Term -> Term
alphaRename v1 v2 = subVar v1 (V v2)
