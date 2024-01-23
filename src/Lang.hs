module Lang
  ( Type,
    GlobalName,
    Var (..),
    Term (..),
    TermValue (..),
    TermData (..),
    PatValue,
    TypeValue,
    Loc (..),
    Pos (..),
    Pat,
    Item (..),
    DataItem (..),
    CtorItem (..),
    DeclItem (..),
    Program (..),
    Clause (..),
    mapTerm,
    HasLoc (..),
    mapTermM,
    clausePats,
    prependPatToClause,
    piTypeToList,
    listToPiType,
    listToApp,
    itemName,
    isValidPat,
    termLoc,
    genTerm,
    termDataAt,
    locatedAt,
    implicitMap,
    varName,
  )
where

import Control.Monad.Identity (runIdentity)
import Data.List (intercalate)
import Data.Maybe (fromMaybe)

-- | Type alias for terms that are expected to be types (just for documentation purposes).
type Type = Term

-- | Type alias for terms that are expected to be patterns (just for documentation purposes).
type Pat = Term

-- | A global name is a string.
type GlobalName = String

-- | A variable
-- Represented by a string name and a unique integer identifier (no shadowing).
data Var = Var String Int deriving (Eq)

-- | Get the name of a variable.
varName :: Var -> String
varName (Var s _) = s

-- | A term
data TermValue
  = -- Dependently-typed lambda calculus with Pi and Sigma:
    PiT Var Type Term
  | Lam Var Term
  | App Term Term
  | SigmaT Var Type Term
  | Pair Term Term
  | -- | Type of types (no universe polymorphism)
    TyT
  | -- | Variable
    V Var
  | -- | Wildcard pattern
    Wild
  | -- | Global variable (declaration)
    Global String
  | -- | Hole identified by an integer
    Hole Var
  deriving (Eq)

-- | A term with associated data.
data Term = Term {termValue :: TermValue, termData :: TermData} deriving (Eq)

-- | Alias for type values (just for documentation purposes)
type TypeValue = TermValue

-- | Alias for pattern values (just for documentation purposes)
type PatValue = TermValue

-- | An optional location in the source code, represented by a start (inclusive) and
-- end (exclusive) position.
data Loc = NoLoc | Loc Pos Pos deriving (Eq)

-- | A monoid instance for locations, that gets the maximum span.
instance Monoid Loc where
  mempty = NoLoc

instance Semigroup Loc where
  NoLoc <> NoLoc = NoLoc
  NoLoc <> Loc s e = Loc s e
  Loc s e <> NoLoc = Loc s e
  Loc s1 e1 <> Loc s2 e2 = Loc (min s1 s2) (max e1 e2)

-- | A position in the source code, represented by a line and column number.
data Pos = Pos Int Int deriving (Eq)

-- | An ordering for positions, that gets the minimum position.
instance Ord Pos where
  Pos l1 c1 <= Pos l2 c2 = l1 < l2 || (l1 == l2 && c1 <= c2)

-- | Get the starting position of a location.
startPos :: Loc -> Maybe Pos
startPos NoLoc = Nothing
startPos (Loc start _) = Just start

-- | Get the ending position of a location.
endPos :: Loc -> Maybe Pos
endPos NoLoc = Nothing
endPos (Loc _ end) = Just end

-- | Auxiliary data contained alongside a term.
--
-- For now stores only the location in the source code, but will
-- be extended to store type information too.
newtype TermData = TermData {loc :: Loc} deriving (Eq)

-- | Empty term data.
emptyTermData :: TermData
emptyTermData = TermData NoLoc

-- | Class of types that have a location.
class HasLoc a where
  getLoc :: a -> Loc

instance HasLoc Term where
  getLoc = termLoc

instance HasLoc TermData where
  getLoc = loc

instance HasLoc Loc where
  getLoc = id

-- | Create a term with the given value and location.
locatedAt :: (HasLoc a) => a -> TermValue -> Term
locatedAt a t = Term t (termDataAt (getLoc a))

-- | Create term data with the given location.
termDataAt :: (HasLoc a) => a -> TermData
termDataAt = TermData . getLoc

-- | Get the term data from a term.
termLoc :: Term -> Loc
termLoc = loc . termData

-- | Generated term, no data
genTerm :: TermValue -> Term
genTerm t = Term t emptyTermData

-- | Convert a pi type to a list of types and the return type.
piTypeToList :: Type -> ([(Var, Type)], Type)
piTypeToList (Term (PiT v ty1 ty2) _) = let (tys, ty) = piTypeToList ty2 in ((v, ty1) : tys, ty)
piTypeToList t = ([], t)

-- | Convert a list of types and the return type to a pi type.
listToPiType :: ([(Var, Type)], Type) -> Type
listToPiType ([], ty) = ty
listToPiType ((v, ty1) : tys, ty2) = Term (PiT v ty1 (listToPiType (tys, ty2))) emptyTermData

-- | Convert a *non-empty* list of terms to an application term
listToApp :: [Term] -> Term
listToApp = foldl1 (\acc x -> Term (App acc x) (termDataAt (termLoc acc <> termLoc x)))

-- | Convert an application term to a *non-empty* list of terms
appToList :: Term -> [Term]
appToList (Term (App t1 t2) _) = appToList t1 ++ [t2]
appToList t = [t]

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
    ctorItemTy :: Type,
    ctorItemDataName :: String
  }
  deriving (Eq)

-- | A clause is a sequence of patterns followed by a term.
data Clause = Clause [Pat] Term | ImpossibleClause [Pat]
  deriving (Eq)

-- | Get the patterns from a clause.
clausePats :: Clause -> [Pat]
clausePats (Clause pats _) = pats
clausePats (ImpossibleClause pats) = pats

prependPatToClause :: Pat -> Clause -> Clause
prependPatToClause p (Clause ps t) = Clause (p : ps) t
prependPatToClause p (ImpossibleClause ps) = ImpossibleClause (p : ps)

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
    Nothing -> do
      mappedTerm <- case termValue term of
        (PiT v t1 t2) -> PiT v <$> mapTermM f t1 <*> mapTermM f t2
        (Lam v t) -> Lam v <$> mapTermM f t
        (App t1 t2) -> App <$> mapTermM f t1 <*> mapTermM f t2
        (SigmaT v t1 t2) -> SigmaT v <$> mapTermM f t1 <*> mapTermM f t2
        (Pair t1 t2) -> Pair <$> mapTermM f t1 <*> mapTermM f t2
        TyT -> return TyT
        Wild -> return Wild
        (V v) -> return $ V v
        (Global s) -> return $ Global s
        (Hole i) -> return $ Hole i
      return (Term mappedTerm (termData term))
    Just t' -> return t'

-- Show instances for pretty printing:
instance Show Var where
  show (Var s _) = s

-- | A set of prelude terms that accept implicit arguments.
implicitMap :: [(String, Int)]
implicitMap =
  [ ("Eq", 1),
    ("LNil", 1),
    ("LCons", 1),
    ("VNil", 1),
    ("VCons", 2),
    ("FS", 1),
    ("FZ", 1),
    ("Nothing", 1),
    ("Just", 1),
    ("Refl", 1),
    ("LTEZero", 1),
    ("LTESucc", 1)
  ]

-- | Prelude globals which have special symbols
constantMap :: [(String, String)]
constantMap =
  [ ("LNil", "[]")
  ]

-- | Prelude terms and types which are infix operators.
infixMap :: [(String, String)]
infixMap =
  [ ("LCons", "::"),
    ("Eq", "=")
  ]

-- | Whether a term is compound, i.e. has spaces inside it (for formatting purposes).
isCompound :: TermValue -> Bool
isCompound (PiT {}) = True
isCompound (Lam _ _) = True
isCompound t@(App _ _) = case unelabApp t of
  [_] -> False
  _ -> True
isCompound (SigmaT {}) = True
isCompound _ = False

-- | Check if a given term is a valid pattern (no typechecking).
isValidPat :: Term -> Bool
isValidPat (Term (App a b) _) = isValidPat a && isValidPat b
isValidPat (Term (Global _) _) = True
isValidPat (Term (V _) _) = True
isValidPat (Term Wild _) = True
isValidPat (Term (Pair p1 p2) _) = isValidPat p1 && isValidPat p2
isValidPat _ = False

-- | Unelaborate an application term.
unelabApp :: TermValue -> [Term]
unelabApp t =
  let lst = appToList (genTerm t)
   in -- Unelaborate implicit arguments
      case lst of
        t'@(Term (Global s) _) : xs
          | Just n <- lookup s implicitMap ->
              let lst' = t' : drop n xs
               in lst'
        _ -> lst

-- | Show a term as a single string (for formatting purposes).
showSingle :: TermValue -> String
showSingle t | isCompound t = "(" ++ show t ++ ")"
showSingle t = show t

instance Show TermValue where
  show (PiT v t1 t2) = "(" ++ show v ++ " : " ++ show t1 ++ ") -> " ++ show t2
  show (Lam v t) = "(\\" ++ show v ++ " => " ++ show t ++ ")"
  show t@(App _ _) = showApp (unelabApp t)
    where
      showApp :: [Term] -> String
      showApp [n, t1, t2]
        | Just s <- lookup (show n) infixMap =
            (showSingle . termValue) t1 ++ " " ++ s ++ " " ++ (showSingle . termValue) t2
      showApp ts = intercalate " " (map (showSingle . termValue) ts)
  show (SigmaT v t1 t2) = "(" ++ show v ++ " : " ++ show t1 ++ ") ** " ++ show t2
  show (Pair t1 t2) = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
  show TyT = "Type"
  show Wild = "_"
  show (V v) = show v
  show (Global s) = fromMaybe s (lookup s constantMap)
  show (Hole i) = "?" ++ show i

instance Show Loc where
  show NoLoc = ""
  show (Loc l c) = show l ++ "--" ++ show c

instance Show Pos where
  show (Pos l c) = show l ++ ":" ++ show c

instance Show TermData where
  show (TermData l) = show l

instance Show Term where
  show (Term t _) = show t

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
      ++ intercalate "\n" (map (\(CtorItem s t _) -> "  | " ++ s ++ " : " ++ show t) ctors)

instance Show DeclItem where
  show (DeclItem v ty clauses) = intercalate "\n" ((v ++ " : " ++ show ty) : map (\c -> v ++ " " ++ show c) clauses)

instance Show Clause where
  show (Clause p t) = intercalate " " (map (showSingle . termValue) p) ++ " = " ++ show t
  show (ImpossibleClause p) = intercalate " " (map (showSingle . termValue) p) ++ " impossible"

instance Show Program where
  show (Program ds) = intercalate "\n\n" $ map show ds
