module Lang
  ( Type,
    GlobalName,
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
    mapPat,
    mapPatM,
    clausePats,
    prependPatToClause,
    piTypeToList,
    listToPiType,
    itemName,
  )
where

import Control.Monad.Identity (runIdentity)
import Data.List (intercalate)
import Text.Parsec.Pos

defaultPos :: SourcePos
defaultPos = newPos "unknown location" 0 0

-- | Type alias for terms that are expected to be types (just for documentation purposes).
type Type = Term

-- | A global name is a string.
type GlobalName = String

-- | A variable
-- Represented by a string name and a unique integer identifier (no shadowing).
data Var = Var String Int deriving (Eq)

data Located a = Located SourcePos a

data LocatedPat = LocatedPat (Located (Pat LocatedPat))

-- | A pattern
data Pat a 
  = -- | Variable binding pattern
    VP Var
  | -- | Wildcard pattern
    WildP
  | -- | Pair pattern
    PairP a a
  | -- Constructors:
    LNilP
  | LConsP a a
  | VNilP
  | VConsP a a
  | FZP
  | FSP a
  | ZP
  | SP a
  | MJustP a
  | MNothingP
  | ReflP a
  | LTEZeroP
  | LTESuccP a
  | CtorP GlobalName [a]
  deriving (Eq)

data LocatedTerm = LocatedTerm (Located (Term LocatedTerm))

type LocatedType = LocatedTerm

-- | A term
data Term t
  = -- Dependently-typed lambda calculus with Pi and Sigma:
    PiT Var t t
  | Lam Var t
  | App t t
  | SigmaT Var t t
  | Pair t t
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
  | ListT t
  | MaybeT t
  | VectT t t 
  | FinT t 
  | EqT t t 
  | LteT t t 
  | -- Constructors:
    FZ
  | FS t 
  | Z
  | S t 
  | LNil
  | LCons t t 
  | VNil
  | VCons t t 
  | MJust t 
  | MNothing
  | Refl t 
  | LTEZero
  | LTESucc t 
  deriving (Eq)

-- | Convert a pi type to a list of types and the return type.
piTypeToList :: LocatedType -> ([(Var, LocatedType)], LocatedType)
piTypeToList (LocatedTerm (Located s (PiT v ty1 ty2))) = let (tys, ty) = piTypeToList ty2 in ((v, ty1) : tys, ty)
piTypeToList t = ([], t)

-- | Convert a list of types and the return type to a pi type.
listToPiType :: ([(Var, LocatedType)], LocatedType) -> LocatedType
listToPiType ([], ty) = ty
listToPiType ((v, ty1) : tys, ty2) = LocatedTerm (Located defaultPos (PiT v ty1 (listToPiType (tys, ty2))))

-- | An item is either a declaration or a data item.
data Item p t
  = Decl (DeclItem p t)
  | Data (DataItem t)
  deriving (Eq)

-- | Get the name of an item.
itemName :: Item p t -> String
itemName (Decl (DeclItem name _ _)) = name
itemName (Data (DataItem name _ _)) = name

-- | A declaration is a sequence of clauses, defining the equations for a function.
data DeclItem p t = DeclItem
  { declName :: String,
    declTy :: Type t,
    declClauses :: [Clause p t]
  }
  deriving (Eq)

-- | A data item is an indexed inductive data type declaration, with a sequence
-- of constructors.
data DataItem a = DataItem
  { dataName :: String,
    dataTy :: Type a,
    dataCtors :: [CtorItem a]
  }
  deriving (Eq)

-- | A constructor item is a constructor name and type.
data CtorItem a = CtorItem
  { ctorItemName :: String,
    ctorItemTy :: Type a,
    ctorItemDataName :: String
  }
  deriving (Eq)

-- | A clause is a sequence of patterns followed by a term.
data Clause p t = Clause [Pat p] (Term t) | ImpossibleClause [Pat p]
  deriving (Eq)

-- | Get the patterns from a clause.
clausePats :: Clause p t -> [Pat p]
clausePats (Clause pats _) = pats
clausePats (ImpossibleClause pats) = pats

prependPatToClause :: Pat p -> Clause p t -> Clause p t
prependPatToClause p (Clause ps t) = Clause (p : ps) t
prependPatToClause p (ImpossibleClause ps) = ImpossibleClause (p : ps)

-- | A program is a sequence of items.
newtype Program p t = Program [Item p t]
  deriving (Eq)

-- | Apply a function to a term, if it is a Just, otherwise return the term.
mapTerm :: (LocatedTerm -> Maybe LocatedTerm) -> LocatedTerm -> LocatedTerm
mapTerm f term = runIdentity $ mapTermM (return . f) term

{-
-- | Apply a function to a term, if it is a Just, otherwise return the term (monadic).
mapTermM :: (Monad m) => (LocatedTerm -> m (Maybe LocatedTerm)) -> LocatedTerm -> m LocatedTerm
mapTermM f term = do
  term' <- f term
  case term' of
    Nothing -> case term of
      (LocatedTerm (Located s (PiT v t1 t2))) -> do r1 <- mapTermM f t1 
                                                    r2 <- mapTermM f t2
                                                    return LocatedTerm (Located s (PiT v r1 r2))
      (LocatedTerm (Located s (Lam v t))) -> do r1 <- mapTermM f t
                                                return LocatedTerm (Located s (Lam v r1))
      (LocatedTerm (Located s (App t1 t2))) -> do r1 <- mapTermM f t1
                                                  r2 <- mapTermM f  t2 
                                                  return LocatedTerm (Located s (App r1 r2))
      (LocatedTerm (Located s (SigmaT v t1 t2))) -> do r1 <- mapTermM f t1
                                                       r2 <- mapTermM f t2    
                                                       return LocatedTerm (Located s (SigmaT v r1 r2))
      (LocatedTerm (Located s (Pair t1 t2))) -> do r1 <- mapTermM f t1
                                                   r2 <- mapTermM f t2
                                                   return LocatedTerm (Located s (Pair r1 r2))
      (LocatedTerm (Located s TyT)) -> return LocatedTerm (Located s TyT)
      (LocatedTerm (Located s (V v))) -> return LocatedTerm (Located s (V v))
      (LocatedTerm (Located s (Global s1))) -> return LocatedTerm (Located s (Global s1))
      (LocatedTerm (Located s (Hole i))) -> return LocatedTerm (Located s (Hole i))
      (LocatedTerm (Located s NatT)) -> return LocatedTerm (Located s NatT)
      (LocatedTerm (Located s (ListT t))) -> do r1 <- mapTermM f t 
                                                return LocatedTerm (Located s (ListT r1))
      (LocatedTerm (Located s (MaybeT t))) -> do r1 <- mapTermM f t
                                                 return LocatedTerm (Located s (MaybeT r1))
      (LocatedTerm (Located s (VectT t n))) -> do r1 <- mapTermM f t
                                                  r2 <- mapTermM f n
                                                  return LocatedTerm (Located s (VectT r1 r2))
      (LocatedTerm (Located s (FinT t))) -> do r1 <- mapTermM f t
                                               return LocatedTerm (Located s (FinT r1))
      (LocatedTerm (Located s (EqT t1 t2))) -> do r1 <- mapTermM f t1
                                                  r2 <- mapTermM f t2
                                                  return LocatedTerm (Located s (EqT r1 r2))
      (LocatedTerm (Located s (LteT t1 t2))) -> do r1 <- mapTermM f t1
                                                   r2 <- mapTermM f t2
                                                   return LocatedTerm (Located s (LteT r1 r2 ))
      (LocatedTerm (Located s FZ)) -> return LocatedTerm (Located s FZ)
      (LocatedTerm (Located s (FS t))) -> do r1 <- mapTermM f t 
                                             return LocatedTerm (Located s (FS r1))
      (LocatedTerm (Located s Z)) -> return LocatedTerm (Located s Z)
      (LocatedTerm (Located s (S t))) -> do r1 <- mapTermM f t
                                            return LocatedTerm (Located s (S r1))
      (LocatedTerm (Located s LNil)) -> return LocatedTerm (Located s LNil)
      (LocatedTerm (Located s (LCons t1 t2))) -> do r1 <- mapTermM f t1
                                                    r2 <- mapTermM f t2
                                                    return LocatedTerm (Located s (LCons r1 r2))
      (LocatedTerm (Located s VNil)) -> return LocatedTerm (Located s VNil)
      (LocatedTerm (Located s (VCons t1 t2))) -> do r1 <- mapTermM f t1
                                                    r2 <- mapTermM f t2
                                                    return LocatedTerm (Located s (VCons r1 r2))
      (LocatedTerm (Located s (MJust t))) -> do r1 <- mapTermM f t
                                                return LocatedTerm (Located s (MJust r1))
      (LocatedTerm (Located s MNothing)) -> return LocatedTerm (Located s MNothing)
      (LocatedTerm (Located s (Refl t))) -> do r1 <- mapTermM f t
                                               return LocatedTerm (Located s (Refl r1))
      (LocatedTerm (Located s LTEZero)) -> return LocatedTerm (Located s LTEZero)
      (LocatedTerm (Located s (LTESucc t))) -> do r1 <- mapTermM f t 
                                                  return LocatedTerm (Located s (LTESucc r1))
    Just t' -> return t'

-- | Apply a function to a pattern, if it is a Just, otherwise return the pattern.
mapPat :: (Pat p -> Maybe (Pat p)) -> Pat p -> Pat p
mapPat f pat = runIdentity $ mapPatM (return . f) pat

-- | Map a function over a pattern, if it is a Just, otherwise return the pattern.
mapPatM :: (Monad m) => (Pat p -> m (Maybe (Pat p))) -> Pat p -> m (Pat p)
mapPatM f pat = do
  pat' <- f pat
  case pat' of
    Nothing -> case pat of
      (VP v) -> return $ VP v
      WildP -> return WildP
      (PairP p1 p2) -> PairP <$> mapPatM f p1 <*> mapPatM f p2
      LNilP -> return LNilP
      (LConsP p1 p2) -> LConsP <$> mapPatM f p1 <*> mapPatM f p2
      VNilP -> return VNilP
      (VConsP p1 p2) -> VConsP <$> mapPatM f p1 <*> mapPatM f p2
      FZP -> return FZP
      (FSP p) -> FSP <$> mapPatM f p
      ZP -> return ZP
      (SP p) -> SP <$> mapPatM f p
      (MJustP p) -> MJustP <$> mapPatM f p
      MNothingP -> return MNothingP
      (ReflP p) -> ReflP <$> mapPatM f p
      LTEZeroP -> return LTEZeroP
      (LTESuccP p) -> LTESuccP <$> mapPatM f p
      (CtorP s ps) -> CtorP s <$> mapM (mapPatM f) ps
    Just t' -> return t'
-}
-- Show instances for pretty printing:
instance Show Var where
  show (Var s _) = s

instance Show a => Show (Pat a) where
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
  show (CtorP s ps) = "(" ++ s ++ (if null ps then "" else " ") ++ unwords (map show ps) ++ ")"

instance Show a => Show (Term a) where
  show (PiT v t1 t2) = "(" ++ show v ++ " : " ++ show t1 ++ ") -> " ++ show t2
  show (Lam v t) = "(\\" ++ show v ++ " -> " ++ show t ++ ")"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (SigmaT v t1 t2) = "(" ++ show v ++ " : " ++ show t1 ++ ") ** " ++ show t2
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

instance (Show p, Show t) => Show (Item p t) where
  show (Decl d) = show d
  show (Data d) = show d

instance (Show t) => Show (DataItem t) where
  show (DataItem name ty ctors) =
    "data "
      ++ name
      ++ " : "
      ++ show ty
      ++ " where\n"
      ++ intercalate "\n" (map (\(CtorItem s t _) -> "  " ++ s ++ " : " ++ show t) ctors)

instance (Show p, Show t) => Show (DeclItem p t) where
  show (DeclItem v ty clauses) = intercalate "\n" ((v ++ " : " ++ show ty) : map (\c -> v ++ " " ++ show c) clauses)

instance (Show p, Show t) => Show (Clause p t) where
  show (Clause p t) = intercalate " " (map show p) ++ " = " ++ show t
  show (ImpossibleClause p) = intercalate " " (map show p) ++ " impossible"

instance (Show p, Show t) => Show (Program p t) where
  show (Program ds) = intercalate "\n\n" $ map show ds
