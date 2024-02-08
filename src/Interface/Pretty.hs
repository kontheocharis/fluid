module Interface.Pretty (Print (..)) where

import Data.List (intercalate)
import Lang

-- | Typeclass like Show but for syntax.
class Print a where
  printVal :: a -> String

  printSingleVal :: a -> String
  printSingleVal = printVal

-- | Replace each newline with a newline followed by 2 spaces.
indented :: String -> String
indented str
  | (l : ls) <- lines str = intercalate "\n" $ l : map ("  " ++) ls
  | [] <- lines str = ""

instance Print Var where
  printVal (Var s _) = s

instance Print TermValue where
  -- \| Show a term value, with parentheses if it is compound.
  printSingleVal v | (isCompound . getTermValue) v = "(" ++ printVal v ++ ")"
  printSingleVal v = printVal v

  printVal (PiT v t1 t2) = "(" ++ printVal v ++ " : " ++ printVal t1 ++ ") -> " ++ printVal t2
  printVal (Lam v t) = "\\" ++ printVal v ++ " => " ++ printVal t
  printVal (SigmaT v t1 t2) = "(" ++ printVal v ++ " : " ++ printVal t1 ++ ") ** " ++ printVal t2
  printVal (Pair t1 t2) = "(" ++ printVal t1 ++ ", " ++ printVal t2 ++ ")"
  printVal t@(App _ _) = intercalate " " $ map printSingleVal (let (x, xs) = appToList (genTerm t) in x : xs)
  printVal (Case t cs) =
    "case "
      ++ printVal t
      ++ " of\n"
      ++ intercalate
        "\n"
        (map (\(p, c) -> "  | " ++ printSingleVal p ++ " => " ++ indented (printVal c)) cs)
  printVal TyT = "Type"
  printVal Wild = "_"
  printVal (V v) = printVal v
  printVal (Global s) = s
  printVal (Hole i) = "?" ++ printVal i
  printVal (Meta i) = "!" ++ printVal i
  printVal NatT = "Nat"
  printVal (ListT t) = "List " ++ printSingleVal t
  printVal (MaybeT t) = "Maybe " ++ printSingleVal t
  printVal (VectT t n) = "Vect " ++ printSingleVal t ++ " " ++ printSingleVal n
  printVal (FinT t) = "Fin " ++ printSingleVal t
  printVal (EqT t1 t2) = printVal t1 ++ " = " ++ printVal t2
  printVal (LteT t1 t2) = "LTE " ++ printSingleVal t1 ++ " " ++ printSingleVal t2
  printVal FZ = "FZ"
  printVal (FS t) = "FS " ++ printSingleVal t
  printVal Z = "Z"
  printVal (S t) = "S " ++ printSingleVal t
  printVal LNil = "[]"
  printVal (LCons t1 t2) = printVal t1 ++ "::" ++ printVal t2
  printVal VNil = "VNil"
  printVal (VCons t1 t2) = "VCons " ++ printSingleVal t1 ++ " " ++ printSingleVal t2
  printVal (MJust t) = "Just " ++ printSingleVal t
  printVal MNothing = "Nothing"
  printVal (Refl t) = "Refl " ++ printSingleVal t
  printVal LTEZero = "LTEZero"
  printVal (LTESucc t) = "LTESucc " ++ printSingleVal t

instance Print Loc where
  printVal NoLoc = ""
  printVal (Loc l c) = show l ++ "--" ++ show c

instance Print Pos where
  printVal (Pos l c) = show l ++ ":" ++ show c

instance Print TermData where
  printVal (TermData l Nothing) = "loc=" ++ printVal l ++ ", type=" ++ "Nothing"
  printVal (TermData l (Just t)) = "loc=" ++ printVal l ++ ", type=" ++ "Just " ++ printSingleVal t

instance Print Term where
  printVal (Term t _) = printVal t --  ++ " " ++ printTermData d

  printSingleVal (Term t _) = printSingleVal t

instance Print Item where
  printVal (Decl d) = printVal d
  printVal (Data d) = printVal d

instance Print DeclItem where
  printVal (DeclItem v ty clauses _) = intercalate "\n" ((v ++ " : " ++ printVal ty) : map (\c -> v ++ " " ++ printVal c) clauses)

instance Print DataItem where
  printVal (DataItem name ty ctors) =
    "data "
      ++ name
      ++ " : "
      ++ printVal ty
      ++ " where\n"
      ++ intercalate "\n" (map (\(CtorItem s t _) -> "  | " ++ s ++ " : " ++ indented (printVal t)) ctors)

instance Print CtorItem where
  printVal (CtorItem name ty _) = name ++ " : " ++ printVal ty

instance Print Clause where
  printVal (Clause p t _) = intercalate " " (map printSingleVal p) ++ " = " ++ printVal t
  printVal (ImpossibleClause p _) = intercalate " " (map printSingleVal p) ++ " impossible"

instance Print Program where
  printVal (Program ds) = intercalate "\n\n" $ map printVal ds
