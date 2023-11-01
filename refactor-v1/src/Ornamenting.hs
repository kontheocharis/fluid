module Ornamenting (ornamentDecl, ornamentType) where

import Lang (Clause (..), Decl (..), Pat (..), Term (..), Type, Var (..), mapTerm)
import Vars (var)

-- | Ornament a declaration.
ornamentDecl :: Decl -> [Decl]
ornamentDecl (Decl comment name ty clauses) = [ornDecl, indexPropDecl]
  where
    (tyOrn, i) = ornamentType ty
    indexPropDeclName = name ++ "Indices"
    indicesAndPropLength = i + 1
    indexPropDecl = generateIndicesPropDecl indexPropDeclName i 0
    tyOrnWithProp =
      PiT
        (var "prf")
        (foldl (\term v -> App term (V (var ("n" ++ show v)))) (Global indexPropDeclName) [0 .. i - 1])
        tyOrn
    tyOrnWithIndices = foldr (\v t -> PiT (var ("n" ++ show v)) NatT t) tyOrnWithProp [0 .. i - 1]
    ornDecl = Decl comment name tyOrnWithIndices (map (ornamentClause indicesAndPropLength name) clauses)

-- | Ornament a clause.
--
-- This recieves the amount of new variables that have been added to the type
-- signature, and uses this to determine how many new variables to add to the
-- patterns and recursive calls.
ornamentClause :: Int -> String -> Clause -> Clause
ornamentClause newIndices declName clause = case clause of
  Clause pats term -> Clause (replicate newIndices WildP ++ map ornamentPat pats) (ornamentClauseTerm newIndices declName term)
  ImpossibleClause pats -> ImpossibleClause (replicate newIndices WildP ++ map ornamentPat pats)

-- | Ornament a term that appears as part of a clause of an ornamented declaration of the given name.
ornamentClauseTerm :: Int -> String -> Term -> Term
ornamentClauseTerm i declName =
  mapTerm
    ( \t -> case t of
        Global s | s == declName -> Just (foldl (\term v -> App term (Hole v)) (Global s) [0 .. i - 1])
        _ -> Nothing
    )

-- | Ornament a pattern.
ornamentPat :: Pat -> Pat
ornamentPat ZP = FZP
ornamentPat (SP p) = FSP p
ornamentPat VNilP = LNilP
ornamentPat (VConsP p1 p2) = LConsP p1 p2
ornamentPat p = p

-- | Generates a proposition with the given name that relates a set of indices together
--
-- These indices are determined by the given integer i as (n0,..n(i-1)). They
-- are all typed as natural numbers.
--
-- The proof of the proposition is left as a hole of the given numeric index.
generateIndicesPropDecl :: String -> Int -> Int -> Decl
generateIndicesPropDecl name i holeIdx = Decl Nothing name piType [holeClause]
  where
    vars = map (\n -> Var ("n" ++ show n) n) [0 .. i - 1]
    piType = foldr (\v ty -> PiT v NatT ty) TyT vars
    holeClause = Clause (map VP vars) (Hole holeIdx)

-- | Ornament a type signature.
--
-- This handles ornamentable types such as Nat and List, and recurses into pi types.
-- Returns a pair of the ornamented type and the next unused variable index.
ornamentType :: Type -> (Type, Int)
ornamentType ty = ornamentType' ty 0
  where
    ornamentType' :: Type -> Int -> (Type, Int)
    ornamentType' NatT i = (FinT (V (var ("n" ++ show i))), i + 1)
    ornamentType' (ListT t) i = (VectT t (V (var ("n" ++ show i))), i + 1)
    ornamentType' (PiT v t1 t2) i = (PiT v ot1 ot2, i2)
      where
        (ot1, i1) = ornamentType' t1 i
        (ot2, i2) = ornamentType' t2 i1
    ornamentType' t i = (t, i)
