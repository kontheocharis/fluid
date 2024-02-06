module Refactoring.TraverseUtils where

import Refactoring.Utils

import Lang

import GHC.Generics (Generic)
import Data.Generics (Data)
import Data.Typeable (Typeable)
import Generics.SYB hiding (Generic, Refl)
import Debug.Trace

type SimpPos = (Int, Int)

within :: Pos -> Loc -> Bool
within l (Loc s e) = l >= s && l <= e

locToTerm :: (Data t)
            => Pos 
            -> t
            -> Maybe Term
locToTerm p t = 
   Generics.SYB.something (Nothing `Generics.SYB.mkQ` termBind) t
  where
     termBind term@((Term (V (Var name id)) d)) 
       | Just p == startPos (getLoc d) = -- && Just p <= endPos (getLoc d) =
        Just term 
       | otherwise = Nothing
     termBind _ = Nothing 

-- Find the declaring clause for a term
termToClause :: (Data t)
            => Term 
            -> t 
            -> Maybe Clause
termToClause (Term t d) prog = 
    Generics.SYB.something (Nothing `Generics.SYB.mkQ` inClause) prog 
   where
    inClause x@(Clause pats te (Loc start end)) 
      | getLinePos (startPos (getLoc d)) >= getLinePos (Just start) && 
        getColPos (startPos (getLoc d)) >= getColPos (Just start) &&
        getLinePos (endPos (getLoc d)) <= getLinePos (Just end) &&
        getColPos (endPos (getLoc d)) <= getColPos (Just end) = Just $ Clause pats te (Loc start end)
    inClause _ = Nothing

termToCase :: Pos -> Term -> Program -> Maybe Term
termToCase l t p =
  do
    (Clause _ t' _) <- termToClause t p
    Generics.SYB.something (Nothing `Generics.SYB.mkQ` inCase) t'
  where
    inCase :: Term -> Maybe Term
    inCase x@(Term (Case c cs) td)
      | within l (loc td) = Just x
    inCase _ = Nothing


-- Find the declaring clause for a term
termToDeclItem :: (Data t)
            => Term 
            -> t 
            -> Maybe DeclItem
termToDeclItem (Term t d) prog = 
    Generics.SYB.something (Nothing `Generics.SYB.mkQ` inItem) prog 
   where
    inItem x@(DeclItem declName declTy declClauses (Loc start end))
      | getLinePos (startPos (getLoc d)) >= getLinePos (Just start) && 
   --     getColPos (startPos (getLoc d)) >= getColPos (Just start) &&
        getLinePos (endPos (getLoc d)) <= getLinePos (Just end) = Just $ x 
   --      getColPos (endPos (getLoc d)) <= getColPos (Just end) = Just $ x -}
    inItem _ = Nothing

getTypeName :: (Data t) 
          => Term 
          -> t 
          -> Maybe String 
getTypeName (Term t d) prog =
        Generics.SYB.something (Nothing `Generics.SYB.mkQ` inGlobal) prog
  where 
    inGlobal x@(Global s) = Just s 
    inGlobal _ = Nothing  


-- returns a type declaration based on the type of a term
stringToDataItem :: (Data t)
            => String 
            -> t
            -> Maybe DataItem 
stringToDataItem name prog = 
    Generics.SYB.something (Nothing `Generics.SYB.mkQ` inItems) prog 
      where 
        inItems d@(DataItem tyName ty ctors) 
          | name == tyName = Just d
        inItems _ = Nothing

-- returns the constructors associated to a data type
typeToCtrs :: DataItem -> [CtorItem]
typeToCtrs (DataItem _ _ c) = c

ctrToName :: CtorItem -> String 
ctrToName (CtorItem n _ _ ) = n

ctrToType :: CtorItem -> Type 
ctrToType (CtorItem _ t _ ) = t

termToId :: TermValue -> Int 
termToId (V (Var name id)) = id
termToId _ = error "can't find ID for term"

insertClauses :: [Clause]  -- the original clauses 
              -> Clause    -- the clause to replace with the insertion
              -> [Clause]  -- the clauses to insert
              -> [Clause]  -- the result 
insertClauses [] c csI = []
insertClauses (cl:cs) c csI 
  | cl == c = csI ++ cs 
  | otherwise = cl : insertClauses cs c csI  


replaceTerm:: (Data t, Monad m) => 
              TermValue -- TermValue to replace
           -> TermValue -- what to replace with 
           -> t 
           -> m t  
replaceTerm term t1 prog =
  do
     everywhereM (mkM transformTerm) prog
     
  where
     transformTerm :: (Monad m) => TermValue -> m TermValue
     transformTerm term2
      | term2 == term = return t1
      | otherwise     = return term2

replaceVar :: (Data t, Monad m) =>
              TermValue -- TermValue to replace Variable with
           -> TermValue -- what to replace with 
           -> Int       -- index of variable to replace 
           -> t 
           -> m t 
replaceVar term t1 var prog = 
  do
    everywhereM (mkM transformVar) prog 
  where 
    transformVar t@(V (Var n id))
      | id == var = return t1 
      | otherwise = return t
    transformVar t = return t


replaceDeclItem :: (Data t, Monad m) => 
              DeclItem -- TermValue to replace
           -> DeclItem  -- what to replace with 
           -> t 
           -> m t  
replaceDeclItem d d2 prog =
  do
     everywhereM (mkM transformDecl) prog
     
  where
     transformDecl :: (Monad m) => DeclItem -> m DeclItem
     transformDecl decl2
      | decl2 == d    = return d2
      | otherwise     = return decl2      