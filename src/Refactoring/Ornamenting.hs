{-# LANGUAGE LambdaCase #-}

module Refactoring.Ornamenting (ornamentDeclItem, ornamentType) where

import Checking.Vars (var)
import Lang (Clause (..), DeclItem (..), MapResult (Continue, Replace), Pat, Term (..), TermValue (..), Type, Var (..), genTerm, mapTerm, piTypeToList)

-- | Ornament a declaration.
ornamentDeclItem :: DeclItem -> (DeclItem, DeclItem)
ornamentDeclItem (DeclItem name ty clauses) = (ornItem, indexPropItem)
  where
    (tyOrn, i) = ornamentType ty
    indexPropItemName = name ++ "Indices"
    indicesAndPropLength = i + 1
    indexPropItem = generateIndicesPropItem indexPropItemName i
    tyOrnWithProp =
      genTerm
        ( PiT
            (var "prf")
            (foldl (\term v -> genTerm (App term (genTerm (V (var ("n" ++ show v)))))) (genTerm (Global indexPropItemName)) [0 .. i - 1])
            tyOrn
        )
    tyOrnWithIndices = foldr (\v t -> genTerm (PiT (var ("n" ++ show v)) (genTerm NatT) t)) tyOrnWithProp [0 .. i - 1]

    (_, ornRetType) = piTypeToList tyOrn
    ornClauses = map (ornamentClause indicesAndPropLength name ornRetType) clauses
    ornItem = DeclItem name tyOrnWithIndices ornClauses

-- | Ornament a clause.
--
-- This recieves the amount of new variables that have been added to the type
-- signature, and uses this to determine how many new variables to add to the
-- patterns and recursive calls.
ornamentClause :: Int -> String -> Type -> Clause -> Clause
ornamentClause newIndices decl newRetType clause = case clause of
  Clause pats term -> Clause (replicate newIndices (genTerm Wild) ++ map ornamentPat pats) (ornamentClauseTerm newIndices decl newRetType term)
  ImpossibleClause pats -> ImpossibleClause (replicate newIndices (genTerm Wild) ++ map ornamentPat pats)

-- | Ornament a term that appears as part of a clause of an ornamented declaration of the given name.
--
-- This is a best-effort attempt to replace the original term with the ornamented term.
ornamentClauseTerm :: Int -> String -> Type -> Term -> Term
ornamentClauseTerm i decl newRetType term = substitutedRecTerm
  where
    -- First try to fix the type of the outermost term.
    typeFixedTerm = case (termValue newRetType, termValue term) of
      (FinT _, Z) -> FZ
      (FinT _, S n) -> FS (natToFin n)
      (VectT _ _, LNil) -> VNil
      (VectT _ _, LCons h t) -> VCons h (listToVect t)
      _ -> termValue term
    --- Substitute the recursive call with the ornamented recursive call.
    substitutedRecTerm =
      mapTerm
        ( \case
            Term (Global s) d | s == decl -> Replace (foldl (\inner v -> genTerm (App inner (genTerm (Hole (var (show v)))))) (Term (Global s) d) [0 .. i - 1])
            _ -> Continue
        )
        (genTerm typeFixedTerm)

-- | Ornament a pattern.
ornamentPat :: Pat -> Pat
ornamentPat (Term Z d) = Term FZ d
ornamentPat (Term (S p) d) = Term (FS (natToFin p)) d
ornamentPat (Term VNil d) = Term LNil d
ornamentPat (Term (VCons p1 p2) d) = Term (LCons p1 (listToVect p2)) d
ornamentPat p = p

-- | Convert a fin to a nat.
natToFin :: Term -> Term
natToFin (Term Z d) = Term FZ d
natToFin (Term (S n) d) = Term (FS (natToFin n)) d
natToFin t = t

-- | Convert a list to a vector.
listToVect :: Term -> Term
listToVect (Term LNil d) = Term VNil d
listToVect (Term (LCons h t) d) = Term (VCons h (listToVect t)) d
listToVect t = t

-- | Generates a proposition with the given name that relates a set of indices together
--
-- These indices are determined by the given integer i as (n0,..n(i-1)). They
-- are all typed as natural numbers.
--
-- The proof of the proposition is left as a hole.
generateIndicesPropItem :: String -> Int -> DeclItem
generateIndicesPropItem name i = DeclItem name piType [holeClause]
  where
    vars = map (\n -> Var ("n" ++ show n) n) [0 .. i - 1]
    piType = foldr (\v ty -> genTerm (PiT v (genTerm NatT) ty)) (genTerm TyT) vars
    holeClause = Clause (map (genTerm . V) vars) (genTerm (Hole (var "proof")))

-- | Ornament a type signature.
--
-- This handles ornamentable types such as Nat and List, and recurses into pi types.
-- Returns a pair of the ornamented type and the next unused variable index.
ornamentType :: Type -> (Type, Int)
ornamentType ty = ornamentType' ty 0
  where
    ornamentType' :: Type -> Int -> (Type, Int)
    ornamentType' (Term NatT d) i = (Term (FinT (genTerm (V (var ("n" ++ show i))))) d, i + 1)
    ornamentType' (Term (ListT t) d) i = (Term (VectT t (genTerm (V (var ("n" ++ show i))))) d, i + 1)
    ornamentType' (Term (PiT v t1 t2) d) i = (Term (PiT v ot1 ot2) d, i2)
      where
        (ot1, i1) = ornamentType' t1 i
        (ot2, i2) = ornamentType' t2 i1
    ornamentType' t i = (t, i)
