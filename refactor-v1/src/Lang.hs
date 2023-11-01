module Lang
  ( Type,
    Var (..),
    Pat (..),
    Term (..),
    Decl (..),
    Program (..),
    Clause (..),
    mapTerm,
    clausePats,
  )
where

import Data.List (intercalate)

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
  | -- | Pair pattern
    PairP Pat Pat
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
  | ReflP Pat
  deriving (Eq)

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
  | Refl Term
  deriving (Eq)

-- | A declaration is a sequence of clauses, defining the equations for a function, potentially with a comment.
data Decl = Decl (Maybe String) String Type [Clause]

-- | A clause is a sequence of patterns followed by a term.
data Clause = Clause [Pat] Term | ImpossibleClause [Pat]

-- | Get the patterns from a clause.
clausePats :: Clause -> [Pat]
clausePats (Clause pats _) = pats
clausePats (ImpossibleClause pats) = pats

-- | A program is a sequence of declarations.
newtype Program = Program [Decl]

-- | Apply a function to a term, if it is a Just, otherwise return the term.
mapTerm :: (Term -> Maybe Term) -> Term -> Term
mapTerm f t | Just t' <- f t = t'
mapTerm f (PiT v t1 t2) = PiT v (mapTerm f t1) (mapTerm f t2)
mapTerm f (Lam v t) = Lam v (mapTerm f t)
mapTerm f (App t1 t2) = App (mapTerm f t1) (mapTerm f t2)
mapTerm f (SigmaT v t1 t2) = SigmaT v (mapTerm f t1) (mapTerm f t2)
mapTerm f (Pair t1 t2) = Pair (mapTerm f t1) (mapTerm f t2)
mapTerm _ TyT = TyT
mapTerm _ (V v) = V v
mapTerm _ (Global s) = Global s
mapTerm _ (Hole i) = Hole i
mapTerm _ NatT = NatT
mapTerm f (ListT t) = ListT (mapTerm f t)
mapTerm f (MaybeT t) = MaybeT (mapTerm f t)
mapTerm f (VectT t n) = VectT (mapTerm f t) (mapTerm f n)
mapTerm f (FinT t) = FinT (mapTerm f t)
mapTerm f (EqT t1 t2) = EqT (mapTerm f t1) (mapTerm f t2)
mapTerm _ FZ = FZ
mapTerm f (FS t) = FS (mapTerm f t)
mapTerm _ Z = Z
mapTerm f (S t) = S (mapTerm f t)
mapTerm _ LNil = LNil
mapTerm f (LCons t1 t2) = LCons (mapTerm f t1) (mapTerm f t2)
mapTerm _ VNil = VNil
mapTerm f (VCons t1 t2) = VCons (mapTerm f t1) (mapTerm f t2)
mapTerm f (MJust t) = MJust (mapTerm f t)
mapTerm _ MNothing = MNothing
mapTerm f (Refl t) = Refl (mapTerm f t)

-- Show instances for pretty printing:
instance Show Var where
  show (Var s _) = s

instance Show Pat where
  show (VP v) = show v
  show WildP = "_"
  show (PairP p1 p2) = "(" ++ show p1 ++ ", " ++ show p2 ++ ")"
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
  show (ReflP p) = "(Refl " ++ show p ++ ")"

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
  show (Refl t) = "(Refl " ++ show t ++ ")"

instance Show Decl where
  show (Decl com v ty clauses) =
    intercalate "\n" $
      ( case com of
          Just x -> map ("-- " ++) (lines x)
          Nothing -> []
      )
        ++ ((v ++ " : " ++ show ty) : map (\c -> v ++ " " ++ show c) clauses)

instance Show Clause where
  show (Clause p t) = intercalate " " (map show p) ++ " = " ++ show t
  show (ImpossibleClause p) = intercalate " " (map show p) ++ " impossible"

instance Show Program where
  show (Program ds) = intercalate "\n\n" $ map show ds
