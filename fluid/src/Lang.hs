module Lang
  ( Type,
    Var (..),
    Pat (..),
    Term (..),
    Item (..),
    DataItem (..),
    CtorItem (..),
    DeclItem (..),
    Program (..),
    Clause (..),
    mapTerm,
    mapTermM,
    clausePats,
    piTypeToList,
    termToPat,
    itemName,
  )
where

import Control.Monad.Identity (runIdentity)
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
  | LTEZeroP
  | LTESuccP Pat
  | CtorP CtorId [Pat]
  deriving (Eq)

-- | A data type identifier, referencing the global name of the data type.
newtype DataId = DataId
  { dataIdName :: String
  }
  deriving (Eq)

-- | A constructor identifier
data CtorId = CtorId
  { ctorDataId :: DataId,
    ctorIdx :: Int,
    ctorName :: String
  }
  deriving (Eq)

-- | A term
data Term
  = -- Dependently-typed lambda calculus with Pi and Sigma:
    PiT Var Type Type
  | Lam Var Term
  | App Term Term
  | SigmaT Var Type Type
  | Pair Term Term
  | -- | Inductive data types and constructors:
    DataT DataId [Term]
  | Ctor CtorId [Term]
  | -- | Type of types (no universe polymorphism)
    TyT
  | -- | Variable
    V Var
  | -- | Global variable (declaration)
    Global String
  | -- | Hole identified by an integer
    Hole Var
  | -- Data types:
    NatT
  | ListT Type
  | MaybeT Type
  | VectT Type Term
  | FinT Term
  | EqT Term Term
  | LteT Term Term
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
  | LTEZero
  | LTESucc Term
  deriving (Eq)

-- | Convert a pi type to a list of types and the return type.
piTypeToList :: Type -> ([(Var, Type)], Type)
piTypeToList (PiT v ty1 ty2) = let (tys, ty) = piTypeToList ty2 in ((v, ty1) : tys, ty)
piTypeToList t = ([], t)

-- | An item is either a declaration or a data item.
data Item
  = Decl DeclItem
  | Data DataItem
  deriving (Eq)

-- | Get the name of an item.
itemName :: Item -> String
itemName (Decl (DeclItem name _ _)) = name
itemName (Data (DataItem name _ _)) = name

-- | A declaration is a sequence of clauses, defining the equations for a function.
data DeclItem = DeclItem
  { declName :: String,
    declTy :: Type,
    declClauses :: [Clause]
  }
  deriving (Eq)

-- | A data item is an indexed inductive data type declaration, with a sequence
-- of constructors.
data DataItem = DataItem
  { dataName :: String,
    dataTy :: Type,
    dataCtors :: [CtorItem]
  }
  deriving (Eq)

-- | A constructor item is a constructor name and type.
data CtorItem = CtorItem
  { ctorItemName :: String,
    ctorItemTy :: Type
  }
  deriving (Eq)

-- | A clause is a sequence of patterns followed by a term.
data Clause = Clause [Pat] Term | ImpossibleClause [Pat]
  deriving (Eq)

-- | Get the patterns from a clause.
clausePats :: Clause -> [Pat]
clausePats (Clause pats _) = pats
clausePats (ImpossibleClause pats) = pats

-- | A program is a sequence of items.
newtype Program = Program [Item]
  deriving (Eq)

-- | Apply a function to a term, if it is a Just, otherwise return the term.
mapTerm :: (Term -> Maybe Term) -> Term -> Term
mapTerm f term = runIdentity $ mapTermM (return . f) term

-- | Apply a function to a term, if it is a Just, otherwise return the term (monadic).
mapTermM :: (Monad m) => (Term -> m (Maybe Term)) -> Term -> m Term
mapTermM f term = do
  term' <- f term
  case term' of
    Nothing -> case term of
      (PiT v t1 t2) -> PiT v <$> mapTermM f t1 <*> mapTermM f t2
      (Lam v t) -> Lam v <$> mapTermM f t
      (App t1 t2) -> App <$> mapTermM f t1 <*> mapTermM f t2
      (SigmaT v t1 t2) -> SigmaT v <$> mapTermM f t1 <*> mapTermM f t2
      (Pair t1 t2) -> Pair <$> mapTermM f t1 <*> mapTermM f t2
      (DataT d ts) -> DataT d <$> mapM (mapTermM f) ts
      (Ctor d ts) -> Ctor d <$> mapM (mapTermM f) ts
      TyT -> return TyT
      (V v) -> return $ V v
      (Global s) -> return $ Global s
      (Hole i) -> return $ Hole i
      NatT -> return NatT
      (ListT t) -> ListT <$> mapTermM f t
      (MaybeT t) -> MaybeT <$> mapTermM f t
      (VectT t n) -> VectT <$> mapTermM f t <*> mapTermM f n
      (FinT t) -> FinT <$> mapTermM f t
      (EqT t1 t2) -> EqT <$> mapTermM f t1 <*> mapTermM f t2
      (LteT t1 t2) -> LteT <$> mapTermM f t1 <*> mapTermM f t2
      FZ -> return FZ
      (FS t) -> FS <$> mapTermM f t
      Z -> return Z
      (S t) -> S <$> mapTermM f t
      LNil -> return LNil
      (LCons t1 t2) -> LCons <$> mapTermM f t1 <*> mapTermM f t2
      VNil -> return VNil
      (VCons t1 t2) -> VCons <$> mapTermM f t1 <*> mapTermM f t2
      (MJust t) -> MJust <$> mapTermM f t
      MNothing -> return MNothing
      (Refl t) -> Refl <$> mapTermM f t
      LTEZero -> return LTEZero
      (LTESucc t) -> LTESucc <$> mapTermM f t
    Just t' -> return t'

-- | Convert a term to a pattern, if possible.
termToPat :: Term -> Maybe Pat
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
  show LTEZeroP = "LTEZero"
  show (LTESuccP p) = "(LTESucc " ++ show p ++ ")"
  show (CtorP (CtorId _ _ s) ps) = s ++ " " ++ unwords (map show ps)

instance Show Term where
  show (PiT v t1 t2) = "(" ++ show v ++ " : " ++ show t1 ++ ") -> " ++ show t2
  show (Lam v t) = "(\\" ++ show v ++ " -> " ++ show t ++ ")"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (SigmaT v t1 t2) = "(" ++ show v ++ " : " ++ show t1 ++ ") ** " ++ show t2
  show (Pair t1 t2) = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show (DataT (DataId s) ts) = s ++ " " ++ unwords (map show ts)
  show (Ctor (CtorId _ _ s) ts) = s ++ " " ++ unwords (map show ts)
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
  show (LteT t1 t2) = "LTE " ++ show t1 ++ " " ++ show t2
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
  show LTEZero = "LTEZero"
  show (LTESucc t) = "(LTESucc " ++ show t ++ ")"

instance Show Item where
  show (Decl d) = show d
  show (Data d) = show d

instance Show DataItem where
  show (DataItem name ty ctors) =
    "data "
      ++ name
      ++ " : "
      ++ show ty
      ++ " where\n"
      ++ intercalate "\n" (map (\(CtorItem c t) -> "  " ++ c ++ " : " ++ show t) ctors)

instance Show DeclItem where
  show (DeclItem v ty clauses) = intercalate "\n" ((v ++ " : " ++ show ty) : map (\c -> v ++ " " ++ show c) clauses)

instance Show Clause where
  show (Clause p t) = intercalate " " (map show p) ++ " = " ++ show t
  show (ImpossibleClause p) = intercalate " " (map show p) ++ " impossible"

instance Show Program where
  show (Program ds) = intercalate "\n\n" $ map show ds
