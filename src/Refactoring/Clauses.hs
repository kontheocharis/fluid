module Refactoring.Clauses (expandDeclItemPat, expandDeclItemFully) where

import Lang (Clause (..), DeclItem (..), Pat, Term (..), Type, piTypeToList)

-- | Expand all wildcard patterns in a declaration, one level deep.
expandDeclItemFully :: DeclItem -> DeclItem
expandDeclItemFully decl = foldr expandDeclItemPat decl allPatIndices
  where
    (DeclItem _ _ clauses) = decl
    allPatIndices = case clauses of
      [] -> []
      (Clause ps _ : _) -> [0 .. length ps - 1]
      (ImpossibleClause ps : _) -> [0 .. length ps - 1]

-- | Expand a pattern in a declaration at the given index, one level deep.
expandDeclItemPat :: Int -> DeclItem -> DeclItem
expandDeclItemPat idx (DeclItem n ty clauses) = DeclItem n ty (concatMap (expandClausePat ty idx) clauses)

-- | Expand a pattern in a clause at the given index, one level deep.
expandClausePat :: Type -> Int -> Clause -> [Clause]
expandClausePat ty idx clause = expandedClauses
  where
    (piTypes, _) = piTypeToList ty
    (_, targetType) = piTypes !! idx
    (targetPat, pats, term) = case clause of
      Clause ps t -> (ps !! idx, ps, Just t)
      ImpossibleClause ps -> (ps !! idx, ps, Nothing)
    expandedPats = expandPat targetType targetPat
    expandedClauses =
      map
        ( \p ->
            let ps = take idx pats ++ [p] ++ drop (idx + 1) pats
             in case term of
                  Just t -> Clause ps t
                  Nothing -> ImpossibleClause ps
        )
        expandedPats

-- | Expand a pattern to a list of patterns.
--
-- For now this only expands wildcards.
expandPat :: Type -> Pat -> [Pat]
expandPat NatT Wild = [Z, S Wild]
expandPat (FinT _) Wild = [FZ, FS Wild]
expandPat (ListT _) Wild = [VNil, VCons Wild Wild]
expandPat (MaybeT _) Wild = [MNothing, MJust Wild]
expandPat (VectT _ _) Wild = [LNil, LCons Wild Wild]
expandPat (SigmaT {}) Wild = [Pair Wild Wild]
expandPat _ p = [p]
