module Interface.Pretty where

import Lang
import Data.List (intercalate)

-- | Replace each newline with a newline followed by 2 spaces.
indented :: String -> String
indented str
  | (l : ls) <- lines str = intercalate "\n" $ l : map ("  " ++) ls
  | [] <- lines str = ""

printVar (Var s _) = s

-- | Print a term value, with parentheses if it is compound.
printSingle :: TermValue -> String
printSingle v | (isCompound . getTermValue) v = "(" ++ printTermValue v ++ ")"
printSingle v = printTermValue v

printTermValue :: TermValue -> String 
printTermValue (PiT v t1 t2) = "(" ++ printVar v ++ " : " ++ printTerm t1 ++ ") -> " ++ printTerm t2
printTermValue (Lam v t) = "\\" ++ printVar v ++ " => " ++ printTerm t
printTermValue (SigmaT v t1 t2) = "(" ++ printVar v ++ " : " ++ printTerm t1 ++ ") ** " ++ printTerm t2
printTermValue (Pair t1 t2) = "(" ++ printTerm t1 ++ ", " ++ printTerm t2 ++ ")"
printTermValue t@(App _ _) = intercalate " " $ map printTerm (let (x, xs) = appToList (genTerm t) in x : xs)
printTermValue (Case t cs) =
    "case "
      ++ printTerm t
      ++ " of\n"
      ++ intercalate
        "\n"
        (map (\(p, c) -> "  | " ++ printTerm p ++ " => " ++ indented (printTerm c)) cs)
printTermValue TyT = "Type"
printTermValue Wild = "_"
printTermValue (V v) = printVar v
printTermValue (Global s) = s
printTermValue (Hole i) = "?" ++ printVar i
printTermValue (Meta i) = "!" ++ printVar i
printTermValue NatT = "Nat"
printTermValue (ListT t) = "List " ++ printTerm t
printTermValue (MaybeT t) = "Maybe " ++ printTerm t
printTermValue (VectT t n) = "Vect " ++ printTerm t ++ " " ++ printTerm n
printTermValue (FinT t) = "Fin " ++ printTerm t
printTermValue (EqT t1 t2) = printTerm t1 ++ " = " ++ printTerm t2
printTermValue (LteT t1 t2) = "LTE " ++ printTerm t1 ++ " " ++ printTerm t2
printTermValue FZ = "FZ"
printTermValue (FS t) = "FS " ++ printTerm t
printTermValue Z = "Z"
printTermValue (S t) = "S " ++ printTerm t
printTermValue LNil = "[]"
printTermValue (LCons t1 t2) = printTerm t1 ++ "::" ++ printTerm t2
printTermValue VNil = "VNil"
printTermValue (VCons t1 t2) = "VCons " ++ printTerm t1 ++ " " ++ printTerm t2
printTermValue (MJust t) = "Just " ++ printTerm t
printTermValue MNothing = "Nothing"
printTermValue (Refl t) = "Refl " ++ printTerm t
printTermValue LTEZero = "LTEZero"
printTermValue (LTESucc t) = "LTESucc " ++ printTerm t

printLoc NoLoc = ""
printLoc (Loc l c) = show l ++ "--" ++ show c

printPos (Pos l c) = show l ++ ":" ++ show c

printTermData (TermData l Nothing) = "loc=" ++ printLoc l ++ ", type=" ++ "Nothing"
printTermData (TermData l (Just t)) = "loc=" ++ printLoc l ++ ", type=" ++ "Just " ++ printTerm t


printTerm (Term t d) = printTermValue t ++ " " ++ printTermData d

printItem (Decl d) = printDeclItem d
printItem (Data d) = printDataItem d

printDataItem (DataItem name ty ctors) =
    "data "
      ++ name
      ++ " : "
      ++ printTerm ty
      ++ " where\n"
      ++ intercalate "\n" (map (\(CtorItem s t _) -> "  | " ++ s ++ " : " ++ printTerm t) ctors)

printDeclItem (DeclItem v ty clauses) = intercalate "\n" ((v ++ " : " ++ printTerm ty) : map (\c -> v ++ " " ++ printClause c) clauses)

printClause (Clause p t l ) = intercalate " " (map printTerm p) ++ " = " ++ printTerm t 
printClause (ImpossibleClause p l) = intercalate " " (map printTerm p) ++ " impossible"

printProgram (Program ds) = intercalate "\n\n" $ map printItem ds
