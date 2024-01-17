module Parsing.Resolution
  ( resolveGlobals,
    resolveGlobalsInItem,
    resolveGlobalsInClause,
  )
where

import Checking.Context (GlobalCtx, lookupItemOrCtor)
import Lang
  ( Clause (Clause, ImpossibleClause),
    CtorItem (..),
    DataItem (..),
    DeclItem (..),
    Item (..),
    Term (..),
    Var (..),
    mapTerm,
  )

-- | Resolve global variables in a term.
resolveGlobals :: GlobalCtx -> Term -> Term
resolveGlobals ctx = mapTerm r
  where
    r (V (Var v _)) = case lookupItemOrCtor v ctx of
      Just _ -> Just (Global v)
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
  Clause (map (resolveGlobals ctx) pats) (resolveGlobals ctx term)
resolveGlobalsInClause ctx (ImpossibleClause pats) =
  ImpossibleClause (map (resolveGlobals ctx) pats)
