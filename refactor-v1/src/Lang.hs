module Lang (Type, Var (..), Pat (..), Term (..), Decl (..), Program (..), Clause (..)) where

-- | Type alias for terms that are expected to be types (just for documentation purposes).
type Type = Term

-- | A variable
-- Represented by a string name and a unique integer identifier (no shadowing).
data Var = Var String Int deriving (Eq)

-- | A pattern
data Pat
  = -- | Variable binding pattern
    VP Var
  | -- | Wildcard pattern
    WildP
  | -- Constructors:
    LNilP
  | LConsP Pat Pat
  | VNilP
  | VConsP Pat Pat
  | FZP
  | FSP Pat
  | ZP
  | SP Pat
  | MJustP Pat
  | MNothingP

-- | A term
data Term
  = -- Dependently-typed lambda calculus with Pi and Sigma:
    PiT Var Type Type
  | Lam Var Term
  | App Term Term
  | SigmaT Var Type Type
  | Pair Term Term
  | -- | Type of types (no universe polymorphism)
    TyT
  | -- | Variable
    V Var
  | -- | Global variable (declaration)
    Global String
  | -- | Hole identified by an integer
    Hole Int
  | -- Data types:
    NatT
  | ListT Type
  | MaybeT Type
  | VectT Type Term
  | FinT Term
  | EqT Term Term
  | -- Constructors:
    FZ
  | FS Term
  | Z
  | S Term
  | LNil
  | LCons Term Term
  | VNil
  | VCons Term Term
  | MJust Term
  | MNothing

-- | A declaration is a sequence of clauses, defining the equations for a function.
data Decl = Decl String Type [Clause]

-- | A clause is a sequence of patterns followed by a term.
data Clause = Clause [Pat] Term

-- | A program is a sequence of declarations.
newtype Program = Program [Decl]

-- Show instances for pretty printing:
instance Show Var where
  show (Var s _) = s

instance Show Pat where
  show (VP v) = show v
  show WildP = "_"
  show LNilP = "[]"
  show (LConsP p1 p2) = "(" ++ show p1 ++ "::" ++ show p2 ++ ")"
  show VNilP = "[]"
  show (VConsP p1 p2) = "(" ++ show p1 ++ "::" ++ show p2 ++ ")"
  show FZP = "FZ"
  show (FSP p) = "(FS " ++ show p ++ ")"
  show ZP = "Z"
  show (SP p) = "(S " ++ show p ++ ")"
  show (MJustP p) = "(Just " ++ show p ++ ")"
  show MNothingP = "Nothing"

instance Show Term where
  show (PiT v t1 t2) = "(" ++ show v ++ " : " ++ show t1 ++ ") -> " ++ show t2
  show (Lam v t) = "(\\" ++ show v ++ " -> " ++ show t ++ ")"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (SigmaT v t1 t2) = "(" ++ show v ++ " : " ++ show t1 ++ ") * " ++ show t2
  show (Pair t1 t2) = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show TyT = "Type"
  show (V v) = show v
  show (Global s) = s
  show (Hole i) = "?" ++ show i
  show NatT = "Nat"
  show (ListT t) = "[" ++ show t ++ "]"
  show (MaybeT t) = "Maybe " ++ show t
  show (VectT t n) = "Vect " ++ show t ++ " " ++ show n
  show (FinT t) = "Fin " ++ show t
  show (EqT t1 t2) = show t1 ++ " = " ++ show t2
  show FZ = "FZ"
  show (FS t) = "(FS " ++ show t ++ ")"
  show Z = "Z"
  show (S t) = "(S " ++ show t ++ ")"
  show LNil = "[]"
  show (LCons t1 t2) = "(" ++ show t1 ++ "::" ++ show t2 ++ ")"
  show VNil = "[]"
  show (VCons t1 t2) = "(" ++ show t1 ++ "::" ++ show t2 ++ ")"
  show (MJust t) = "(Just " ++ show t ++ ")"
  show MNothing = "Nothing"

instance Show Decl where
  show (Decl v ty clauses) = unlines $ (v ++ " : " ++ show ty) : map (\c -> v ++ " " ++ show c) clauses

instance Show Clause where
  show (Clause p t) = unwords (map show p) ++ " = " ++ show t

instance Show Program where
  show (Program ds) = unlines $ map show ds
