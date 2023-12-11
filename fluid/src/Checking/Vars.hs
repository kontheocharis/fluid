{-# LANGUAGE FlexibleInstances #-}

module Checking.Vars (var, Sub (..), Subst, sub, subVar, alphaRename, noSub, subSize, insertSub, lookupSub, subInM) where

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

-- | The size of a substitution.
subSize :: Sub -> Int
subSize (Sub s) = length s

-- | Insert into a substitution.
insertSub :: Var -> Term -> Sub -> Sub
insertSub v t (Sub s) = Sub ((v, t) : s)

-- | Get an element from a substitution.
lookupSub :: Var -> Sub -> Maybe Term
lookupSub v (Sub s) = lookup v s

instance Monoid Sub where
  mempty = noSub

instance Semigroup Sub where
  -- This is not a particularly smart way to do this, but it works.
  (<>) (Sub s1) (Sub s2) = Sub (as ++ bs)
    where
      Sub as = sub (Sub s2) (Sub s1)
      Sub bs = sub (Sub s1) (Sub s2)

-- | A typeclass for things that can be substituted.
class Subst a where
  -- | Apply a `Sub` to a term.
  sub :: Sub -> a -> a
  sub (Sub ((v, t') : ss)) t = sub (Sub ss) (subVar v t' t)
  sub (Sub []) t = t

  -- | Substitute a variable for a term in a term.
  subVar :: Var -> Term -> a -> a

  -- | Alpha rename a variable in a term.
  alphaRename :: Var -> Var -> a -> a
  alphaRename v1 v2 = subVar v1 (V v2)

instance Subst Term where
  subVar v t' =
    mapTerm
      ( \t'' -> case t'' of
          V v' | v == v' -> Just t'
          Hole v' | v == v' -> Just t'
          PiT v' ty t | v == v' -> Just (PiT v' (subVar v t' ty) t)
          Lam v' t | v == v' -> Just (Lam v' (subVar v t' t))
          SigmaT v' ty t | v == v' -> Just (SigmaT v' (subVar v t' ty) t)
          _ -> Nothing
      )

-- | Substitute in a term mappable.
subVarInM :: (Monad m, TermMappable t) => Var -> Term -> t -> m t
subVarInM v t' =
  mapTermMappableM
    ( \t'' -> case t'' of
        V v' | v == v' -> return $ Just t'
        Hole v' | v == v' -> return $ Just t'
        _ -> return Nothing
    )

-- | Substitute in a term mappable.
subInM :: (Monad m, TermMappable t) => Sub -> t -> m t
subInM (Sub ((v, t') : ss)) t = do
  t'' <- subVarInM v t' t
  subInM (Sub ss) t''
subInM (Sub []) t = return t

instance Subst Sub where
  subVar v' t' (Sub ((v, t) : s)) = Sub ((v, subVar v' t' t) : let Sub rs = subVar v' t' (Sub s) in rs)
  subVar _ _ (Sub []) = Sub []
