module Interface.Pretty where

import Lang
import Data.List (intercalate)

-- | Replace each newline with a newline followed by 2 spaces.
indented :: String -> String
indented str
  | (l : ls) <- lines str = intercalate "\n" $ l : map ("  " ++) ls
  | [] <- lines str = ""

printVar (Var s _) = s

-- | Show a term value, with parentheses if it is compound.
showSingle :: Term -> String
showSingle v | (isCompound . getTermValue) v =  printTerm 0 v 
showSingle v = printTerm 0 v

printTermValue :: Int -> TermValue -> String 
printTermValue p (PiT v t1 t2) = "(" ++ printVar v ++ " : " ++ printTerm p t1 ++ ") -> " ++ printTerm p t2
printTermValue p (Lam v t) = "\\" ++ printVar v ++ " => " ++ printTerm p t
printTermValue p (SigmaT v t1 t2) = "(" ++ printVar v ++ " : " ++ printTerm p t1 ++ ") ** " ++ printTerm p t2
printTermValue p (Pair t1 t2) = "(" ++ printTerm p t1 ++ ", " ++ printTerm p t2 ++ ")"
printTermValue p t@(App _ _) = if p == 1 then "(" ++ (intercalate " " $ map showSingle (let (x, xs) = appToList (genTerm t) in x : xs)) ++ ")"
                                         else intercalate " " $ map showSingle (let (x, xs) = appToList (genTerm t) in x : xs)
printTermValue p1 (Case t cs) =
    "case "
      ++ printTerm p1 t
      ++ " of\n"
      ++ intercalate
        "\n"
        (map (\(p, c) -> "  | " ++ printTerm p1 p ++ " => " ++ indented (printTerm p1 c)) cs)
printTermValue p TyT = "Type"
printTermValue p Wild = "_"
printTermValue p (V v) = printVar v
printTermValue p (Global s) = s
printTermValue p (Hole i) = "?" ++ printVar i
printTermValue p (Meta i) = "!" ++ printVar i
printTermValue p NatT = "Nat"
printTermValue p (ListT t) = "List " ++ printTerm p t
printTermValue p (MaybeT t) = "Maybe " ++ printTerm p t
printTermValue p (VectT t n) = "Vect " ++ printTerm p t ++ " " ++ printTerm p n
printTermValue p (FinT t) = "Fin " ++ printTerm p t
printTermValue p (EqT t1 t2) = printTerm p t1 ++ " = " ++ printTerm p t2
printTermValue p (LteT t1 t2) = "LTE " ++ printTerm p t1 ++ " " ++ printTerm p t2
printTermValue p FZ = "FZ"
printTermValue p (FS t) = "FS " ++ printTerm p t
printTermValue p Z = "Z"
printTermValue p (S t) = "S " ++ printTerm p t
printTermValue p LNil = "[]"
printTermValue p (LCons t1 t2) = printTerm p t1 ++ "::" ++ printTerm p t2
printTermValue p VNil = "VNil"
printTermValue p (VCons t1 t2) = "VCons " ++ printTerm p t1 ++ " " ++ printTerm p t2
printTermValue p (MJust t) = "Just " ++ printTerm p t
printTermValue p MNothing = "Nothing"
printTermValue p (Refl t) = "Refl " ++ printTerm p t
printTermValue p LTEZero = "LTEZero"
printTermValue p (LTESucc t) = "LTESucc " ++ printTerm p t

printLoc NoLoc = ""
printLoc (Loc l c) = show l ++ "--" ++ show c

printPos (Pos l c) = show l ++ ":" ++ show c

printTermData p (TermData l Nothing) = "loc=" ++ printLoc l ++ ", type=" ++ "Nothing"
printTermData p (TermData l (Just t)) = "loc=" ++ printLoc l ++ ", type=" ++ "Just " ++ printTerm p t


printTerm p (Term t d) = printTermValue p  t --  ++ " " ++ printTermData d

printItem p (Decl d) = printDeclItem p d
printItem p (Data d) = printDataItem p d

printDataItem p (DataItem name ty ctors) =
    "data "
      ++ name
      ++ " : "
      ++ printTerm p ty
      ++ " where\n"
      ++ intercalate "\n" (map (\(CtorItem s t _) -> "  | " ++ s ++ " : " ++ printTerm p t) ctors)

printDeclItem p (DeclItem v ty clauses l) = intercalate "\n" ((v ++ " : " ++ printTerm p ty) : map (\c -> v ++ " " ++ (printClause p) c) clauses)

printClause p1 (Clause p t l ) = intercalate " " (map (printTerm p1) p) ++ " = " ++ printTerm p1 t 
printClause p1 (ImpossibleClause p l) = intercalate " " (map (printTerm p1) p) ++ " impossible"

printProgram (Program ds) = intercalate "\n\n" $ map (printItem 1) ds
