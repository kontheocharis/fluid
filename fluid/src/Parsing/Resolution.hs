module Parsing.Resolution
  ( resolveTerm,
    resolveGlobals,
    resolveGlobalsInItem,
    resolveGlobalsInClause,
    termToPat,
  )
where

import Checking.Context (GlobalCtx, lookupItemOrCtor)
import Lang (Clause (Clause, ImpossibleClause), CtorItem (..), DataItem (..), DeclItem (..), Item (..), Pat (..), Term (..), Var (..), itemName, mapPat, mapTerm)

-- | Resolve global variables in a term.
resolveGlobals :: GlobalCtx -> Term -> Term
resolveGlobals ctx = mapTerm r
  where
    r (V (Var v _)) = case lookupItemOrCtor v ctx of
      Just _ -> Just (Global v)
      Nothing -> Nothing
    r _ = Nothing

-- | Resolve global variables in a pattern.
resolveGlobalsInPat :: GlobalCtx -> Pat -> Pat
resolveGlobalsInPat ctx = mapPat r
  where
    r (VP (Var v _)) = case lookupItemOrCtor v ctx of
      Just (Left item) -> Just (CtorP (itemName item) []) -- this is an error but will be caught later
      Just (Right item) -> Just (CtorP (ctorItemName item) [])
      Nothing -> Nothing
    r _ = Nothing

-- @@Todo: factor out the functions below into `mapProgramM`

-- | Resolve global variables in an item.
resolveGlobalsInItem :: GlobalCtx -> Item -> Item
resolveGlobalsInItem ctx (Decl declItem) = Decl (resolveGlobalsInDeclItem ctx declItem)
resolveGlobalsInItem ctx (Data dataItem) = Data (resolveGlobalsInDataItem ctx dataItem)

-- | Resolve global variables in a data item.
resolveGlobalsInDataItem :: GlobalCtx -> DataItem -> DataItem
resolveGlobalsInDataItem ctx (DataItem name ty ctors) =
  DataItem name (resolveGlobals ctx ty) (map (resolveGlobalsInCtorItem ctx) ctors)

-- | Resolve global variables in a constructor item.
resolveGlobalsInCtorItem :: GlobalCtx -> CtorItem -> CtorItem
resolveGlobalsInCtorItem ctx (CtorItem name ty d) =
  CtorItem name (resolveGlobals ctx ty) d

-- | Resolve global variables in a declaration.
resolveGlobalsInDeclItem :: GlobalCtx -> DeclItem -> DeclItem
resolveGlobalsInDeclItem ctx (DeclItem name ty clauses) =
  DeclItem name (resolveGlobals ctx ty) (map (resolveGlobalsInClause ctx) clauses)

-- | Resolve global variables in a clause.
resolveGlobalsInClause :: GlobalCtx -> Clause -> Clause
resolveGlobalsInClause ctx (Clause pats term) =
  Clause (map (resolveGlobalsInPat ctx) pats) (resolveGlobals ctx term)
resolveGlobalsInClause ctx (ImpossibleClause pats) =
  ImpossibleClause (map (resolveGlobalsInPat ctx) pats)

-- | Resolve the "primitive" data types and constructors in a term.
resolveTerm :: Term -> Term
resolveTerm = mapTerm r
  where
    r (V (Var "Type" _)) = Just TyT
    r (V (Var "Nat" _)) = Just NatT
    r (App (V (Var "List" _)) t1) = Just (ListT (resolveTerm t1))
    r (App (V (Var "Maybe" _)) t1) = Just (MaybeT (resolveTerm t1))
    r (App (App (V (Var "Vect" _)) t1) t2) = Just (VectT (resolveTerm t1) (resolveTerm t2))
    r (App (V (Var "Fin" _)) t1) = Just (FinT (resolveTerm t1))
    r (App (App (V (Var "Eq" _)) t1) t2) = Just (EqT (resolveTerm t1) (resolveTerm t2))
    r (V (Var "Z" _)) = Just Z
    r (App (V (Var "S" _)) t1) = Just (S (resolveTerm t1))
    r (V (Var "FZ" _)) = Just FZ
    r (App (V (Var "FS" _)) t1) = Just (FS (resolveTerm t1))
    r (V (Var "LNil" _)) = Just LNil
    r (App (App (V (Var "LCons" _)) t1) t2) = Just (LCons (resolveTerm t1) (resolveTerm t2))
    r (V (Var "VNil" _)) = Just VNil
    r (App (App (V (Var "VCons" _)) t1) t2) = Just (VCons (resolveTerm t1) (resolveTerm t2))
    r (V (Var "Nothing" _)) = Just MNothing
    r (App (V (Var "Just" _)) t1) = Just (MJust (resolveTerm t1))
    r (App (V (Var "Refl" _)) t1) = Just (Refl (resolveTerm t1))
    r (V (Var "LTEZero" _)) = Just LTEZero
    r (App (V (Var "LTESucc" _)) t1) = Just (LTESucc (resolveTerm t1))
    r _ = Nothing

-- | Convert a term to a pattern, if possible.
termToPat :: Term -> Maybe Pat
termToPat (App (V (Var v _)) b) = do
  b' <- termToPat b
  return $ CtorP v [b']
termToPat (App a b) = do
  a' <- termToPat a
  case a' of
    CtorP v ps -> do
      b' <- termToPat b
      return $ CtorP v (ps ++ [b'])
    _ -> Nothing
termToPat (V (Var "_" _)) = Just WildP
termToPat (V v) = Just $ VP v
termToPat (Pair p1 p2) = do
  p1' <- termToPat p1
  p2' <- termToPat p2
  return $ PairP p1' p2'
termToPat LNil = Just LNilP
termToPat (LCons p1 p2) = do
  p1' <- termToPat p1
  p2' <- termToPat p2
  return $ LConsP p1' p2'
termToPat VNil = Just VNilP
termToPat (VCons p1 p2) = do
  p1' <- termToPat p1
  p2' <- termToPat p2
  return $ VConsP p1' p2'
termToPat FZ = Just FZP
termToPat (FS p) = do
  p' <- termToPat p
  return $ FSP p'
termToPat Z = Just ZP
termToPat (S p) = do
  p' <- termToPat p
  return $ SP p'
termToPat (MJust p) = do
  p' <- termToPat p
  return $ MJustP p'
termToPat MNothing = Just MNothingP
termToPat (Refl p) = do
  p' <- termToPat p
  return $ ReflP p'
termToPat LTEZero = Just LTEZeroP
termToPat (LTESucc p) = do
  p' <- termToPat p
  return $ LTESuccP p'
termToPat _ = Nothing
