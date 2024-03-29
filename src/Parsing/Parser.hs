module Parsing.Parser (parseProgram, parseTerm, parseRefactorArgs) where

import Checking.Context (GlobalCtx (GlobalCtx))
import Control.Monad (void)
import Data.Char (isSpace)
import Data.String
import Data.Text (Text)
import Debug.Trace
import Lang
  ( Clause (..),
    CtorItem (..),
    DataItem (..),
    DeclItem (..),
    GlobalName,
    Item (..),
    Loc (..),
    MapResult (..),
    Pat,
    Pos (..),
    Program (..),
    Term (..),
    TermMappable (..),
    TermValue (..),
    Type,
    Var (..),
    isValidPat,
    listToApp,
    mapTermM,
    termDataAt,
  )
import Parsing.Resolution (resolveGlobalsRec)
import Refactoring.Utils (RefactorArgKind (..), RefactorArgs (RefactorArgs))
import Text.Parsec
  ( Parsec,
    between,
    char,
    choice,
    endOfLine,
    eof,
    getPosition,
    getState,
    many,
    many1,
    modifyState,
    optionMaybe,
    putState,
    runParser,
    satisfy,
    sepBy,
    sourceColumn,
    sourceLine,
    string,
    (<|>),
  )
import Text.Parsec.Char (alphaNum, digit, letter)
import Text.Parsec.Prim (try)
import Text.Parsec.Text ()

-- | Parser state, used for generating fresh variables.
data ParserState = ParserState
  { varCount :: Int,
    -- Keep track of the names of variables so we can resolve them when encountering them.
    names :: [(String, Var)],
    -- Whether we are parsing a pattern.
    parsingPat :: Bool
  }

initialParserState :: ParserState
initialParserState =
  ParserState
    { varCount = 0,
      names = [],
      parsingPat = False
    }

-- | Get a new variable index and increment it.
newVarIndex :: Parser Int
newVarIndex = do
  s <- getState
  let i = varCount s
  putState s {varCount = i + 1}
  return i

-- | Generate a new variable.
registerNewVar :: String -> Parser Var
registerNewVar n = do
  ns <- names <$> getState
  v <- Var n <$> newVarIndex
  modifyState $ \s -> s {names = (n, v) : ns}
  return v

-- | Get an already registered variable or generate a new one.
registerVar :: String -> Parser Var
registerVar n = do
  ns <- names <$> getState
  case lookup n ns of
    Just v -> return v
    Nothing -> do
      v <- Var n <$> newVarIndex
      modifyState $ \s -> s {names = (n, v) : ns}
      return v

-- | Parser type alias.
type Parser a = Parsec Text ParserState a

-- Some helper functions for the parser:

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | Parse whitespace or comments.
white :: Parser ()
white = do
  _ <- many $ (void . try) (satisfy (\c -> isSpace c && c /= '\n')) <|> comment
  return ()

comment :: Parser ()
comment = do
  _ <- try $ do
    reservedOp "--"
    _ <- many (satisfy (/= '\n'))
    return ()
  return ()

-- | Parse vertical whitespace (i.e. a new line) or horizontal whitespace or comments.
anyWhite :: Parser ()
anyWhite = do
  _ <- many $ (void . try) (satisfy isSpace) <|> comment
  return ()

-- | Parse vertical whitespace (i.e. a single new line).
enter :: Parser ()
enter = do
  _ <- endOfLine
  white
  return ()

-- | Reserved identifiers.
reservedIdents :: [String]
reservedIdents = ["data", "where", "case", "of"]

anyIdentifier :: Parser String
anyIdentifier = try $ do
  first <- letter <|> char '_'
  rest <- many (alphaNum <|> char '_' <|> char '\'')
  white
  return $ first : rest

identifier :: Parser String
identifier = try $ do
  name <- anyIdentifier
  if name `elem` reservedIdents
    then fail $ "Identifier " ++ name ++ " is reserved"
    else return name

symbol :: String -> Parser ()
symbol s = try $ do
  _ <- string s
  white
  return ()

reserved :: String -> Parser ()
reserved = symbol

reservedOp :: String -> Parser ()
reservedOp = symbol

comma :: Parser ()
comma = symbol ","

colon :: Parser ()
colon = symbol ":"

-- | Get the current location in the source file.
getPos :: Parser Pos
getPos = do
  s <- getPosition
  return (Pos (sourceLine s) (sourceColumn s))

locatedTerm :: Parser TermValue -> Parser Term
locatedTerm p = do
  start <- getPos
  t <- p
  end <- getPos
  return $ Term t (termDataAt (Loc start end))

-- | Parse a term from a string.
parseTerm :: String -> Either String Term
parseTerm contents = case runParser (term <* eof) initialParserState "" (fromString contents) of
  Left err -> Left $ show err
  Right p -> Right p

-- | Parse a program from its filename and string contents.
parseProgram :: String -> String -> Either String Program
parseProgram filename contents = case runParser (program <* eof) initialParserState filename (fromString contents) of
  Left err -> Left $ show err
  Right p -> Right p

-- | Parse a program.
program :: Parser Program
program = whiteWrap $ do
  ds <- many ((Data <$> dataItem) <|> (Decl <$> declItem))
  -- Resolve the globals after getting all the declarations.
  return $ mapTermMappable (resolveGlobalsRec (GlobalCtx ds)) (Program ds)

-- | Wrap a parser in whitespace.
whiteWrap :: Parser a -> Parser a
whiteWrap p = do
  anyWhite
  x <- p
  anyWhite
  return x

-- | Parse a constructor item.
-- @@Todo: how to deal with indentation?
ctorItem :: GlobalName -> Parser CtorItem
ctorItem d = try $ do
  symbol "|"
  name <- identifier
  _ <- colon
  ty <- term
  enter
  return $ CtorItem name ty d

-- | Parse a data item.
dataItem :: Parser DataItem
dataItem = whiteWrap $ do
  symbol "data"
  (name, ty) <- declSignature
  symbol "where"
  enter
  ctors <- many (ctorItem name)
  return $ DataItem name ty ctors

-- | Parse a declaration.
declItem :: Parser DeclItem
declItem = whiteWrap $ do
  start <- getPos
  (name, ty) <- declSignature
  enter
  clauses <- many (declClause name)
  end <- getPos
  return $ DeclItem name ty clauses (Loc start end)

-- | Parse the type signature of a declaration.
declSignature :: Parser (String, Type)
declSignature = do
  name <- identifier
  _ <- colon
  ty <- term
  return (name, ty)

-- | Parse a clause of a declaration.
declClause :: String -> Parser Clause
declClause name = do
  start <- getPos
  _ <- symbol name
  ps' <- many pat
  -- Check if this is an impossible clause by looking at the last pattern.
  let (im, ps) =
        if null ps'
          then (False, [])
          else case termValue (last ps') of
            (V (Var "impossible" _)) -> (True, init ps')
            _ -> (False, ps')
  clause <-
    if im
      then do
        end <- getPos
        return $ ImpossibleClause ps (Loc start end)
      else do
        reservedOp "="
        c <- Clause ps <$> term
        end <- getPos
        return (c (Loc start end))
  enter
  return clause

-- | Parse a term.
-- Some are grouped to prevent lots of backtracking.
term :: Parser Term
term = do
  t <- choice [caseExpr, piTOrSigmaT, lam, singleAppOrEqTOrCons]
  resolveTerm t

-- | Parse a single term.
--
-- This is a term which never requires parentheses to disambiguate.
singleTerm :: Parser Term
singleTerm = try $ choice [varOrHole, nil, pair, parens term]

-- | Parse a pattern.
pat :: Parser Pat
pat = do
  modifyState $ \s -> s {parsingPat = True}
  t <- singleTerm
  t' <- resolveTerm t
  modifyState $ \s -> s {parsingPat = False}
  if isValidPat t'
    then return t'
    else fail $ "Cannot use term " ++ show t ++ " as a pattern"

-- | Parse a variable.
var :: Parser Var
var = try $ do
  name <- identifier
  registerVar name

-- | Parse a variable binding.
newVar :: Parser Var
newVar = try $ do
  name <- identifier
  registerNewVar name

-- | Generate a fresh variable.
freshVar :: Parser Var
freshVar = try $ do
  idx <- newVarIndex
  return $ Var ("n" ++ show idx) idx

-- | Parse a named parameter like `(n : Nat)`.
named :: Parser (Var, Type)
named =
  ( try . parens $
      do
        optName <- optionMaybe . try $ do
          name <- newVar
          _ <- colon
          return name
        ty <- term
        actualName <- maybe freshVar return optName
        return (actualName, ty)
  )
    <|> try
      ( do
          name <- freshVar
          ty <- singleAppOrEqTOrCons
          return (name, ty)
      )

-- | Parse a pi type or sigma type.
piTOrSigmaT :: Parser Type
piTOrSigmaT = try . locatedTerm $ do
  (name, ty1) <- named
  binderT <- (reservedOp "->" >> return PiT) <|> (reservedOp "**" >> return SigmaT)
  binderT name ty1 <$> term

-- | Parse an application.
app :: Parser Term
app = try $ do
  t <- singleTerm
  ts <- many singleTerm
  return $ listToApp (t, ts)

-- | Parse a single term, application, equality type or list cons.
singleAppOrEqTOrCons :: Parser Term
singleAppOrEqTOrCons = locatedTerm $ do
  t1 <- app
  (reservedOp "=" >> EqT t1 <$> term) <|> (reservedOp "::" >> LCons t1 <$> term) <|> return (termValue t1)

-- | Parse a lambda.
lam :: Parser Term
lam = locatedTerm $ do
  reservedOp "\\"
  v <- newVar
  reservedOp "=>"
  Lam v <$> term

-- | Parse a pair.
pair :: Parser Term
pair = try . locatedTerm . parens $ do
  t1 <- term
  _ <- comma
  Pair t1 <$> term

-- | Parse a variable or hole. Holes are prefixed with a question mark.
varOrHole :: Parser Term
varOrHole = try . locatedTerm $ do
  hole <- optionMaybe $ reservedOp "?"
  v <- var
  case hole of
    Just _ -> return $ Hole v
    Nothing -> return $ V v

-- | Parse a list nil.
nil :: Parser Term
nil = locatedTerm $ do
  reservedOp "[]"
  return LNil

caseExpr :: Parser Term
caseExpr = locatedTerm $ do
  reserved "case"
  t <- term
  reserved "of"
  clauses <- many caseClause
  return $ Case t clauses

caseClause :: Parser (Pat, Term)
caseClause = do
  try (anyWhite >> symbol "|")
  p <- pat
  reservedOp "=>"
  t' <- term
  return (p, t')

-- | Resolve the "primitive" data types and constructors in a term.
resolveTerm :: Term -> Parser Term
resolveTerm = mapTermM r
  where
    r :: Term -> Parser (MapResult Term)
    r (Term (V (Var "_" _)) d) = return . Replace $ Term Wild d
    r (Term (V (Var "Type" _)) d) = return $ Replace (Term TyT d)
    r (Term (V (Var "Nat" _)) d) = return $ Replace (Term NatT d)
    r (Term (App (Term (V (Var "List" _)) _) t1) d) = do
      t1' <- resolveTerm t1
      return (Replace (Term (ListT t1') d))
    r (Term (App (Term (V (Var "Maybe" _)) _) t1) d) = do
      t1' <- resolveTerm t1
      return (Replace (Term (MaybeT t1') d))
    r (Term (App (Term (App (Term (V (Var "Vect" _)) _) t1) _) t2) d) = do
      t1' <- resolveTerm t1
      t2' <- resolveTerm t2
      return (Replace (Term (VectT t1' t2') d))
    r (Term (App (Term (V (Var "Fin" _)) _) t1) d) = do
      t1' <- resolveTerm t1
      return (Replace (Term (FinT t1') d))
    r (Term (App (Term (App (Term (V (Var "Eq" _)) _) t1) _) t2) d) = do
      t1' <- resolveTerm t1
      t2' <- resolveTerm t2
      return (Replace (Term (EqT t1' t2') d))
    r (Term (V (Var "Z" _)) d) = return $ Replace (Term Z d)
    r (Term (App (Term (V (Var "S" _)) _) t1) d) = do
      t1' <- resolveTerm t1
      return (Replace (Term (S t1') d))
    r (Term (V (Var "FZ" _)) d) = return $ Replace (Term FZ d)
    r (Term (App (Term (V (Var "FS" _)) _) t1) d) = do
      t1' <- resolveTerm t1
      return (Replace (Term (FS t1') d))
    r (Term (V (Var "LNil" _)) d) = return $ Replace (Term LNil d)
    r (Term (App (Term (App (Term (V (Var "LCons" _)) _) t1) _) t2) d) = do
      t1' <- resolveTerm t1
      t2' <- resolveTerm t2
      return (Replace (Term (LCons t1' t2') d))
    r (Term (V (Var "VNil" _)) d) = return $ Replace (Term VNil d)
    r (Term (App (Term (App (Term (V (Var "VCons" _)) _) t1) _) t2) d) = do
      t1' <- resolveTerm t1
      t2' <- resolveTerm t2
      return (Replace (Term (VCons t1' t2') d))
    r (Term (V (Var "Nothing" _)) d) = return $ Replace (Term MNothing d)
    r (Term (App (Term (V (Var "Just" _)) _) t1) d) = do
      t1' <- resolveTerm t1
      return (Replace (Term (MJust t1') d))
    r (Term (App (Term (V (Var "Refl" _)) _) t1) d) = do
      t1' <- resolveTerm t1
      return (Replace (Term (Refl t1') d))
    r (Term (V (Var "LTEZero" _)) d) = return $ Replace (Term LTEZero d)
    r (Term (App (Term (V (Var "LTESucc" _)) _) t1) d) = do
      t1' <- resolveTerm t1
      return (Replace (Term (LTESucc t1') d))
    r _ = return Continue

-- | Parse a set of refactoring arguments.
refactorArgs :: Parser RefactorArgs
refactorArgs = RefactorArgs <$> sepBy refactorArg (symbol ",")

-- | Parse a refactoring argument.
refactorArg :: Parser (String, RefactorArgKind)
refactorArg = do
  name <- anyIdentifier
  _ <- symbol "="
  kind <- refactorArgKind
  return (name, kind)

-- | Parse an integer.
integer :: Parser Int
integer = do
  digits <- many1 digit
  return $ read digits

-- | Parse an integer list.
integerList :: Parser [Int]
integerList = between (symbol "[") (symbol "]") $ sepBy integer (symbol ",")

-- | Parse a bool
bool :: Parser Bool
bool = (reserved "True" >> return True) <|> (reserved "False" >> return False)

-- | Parse a position.
position :: Parser Pos
position = do
  line <- integer
  _ <- char ':'
  col <- integer
  return $ Pos line col

-- | Parse a refactoring argument kind.
refactorArgKind :: Parser RefactorArgKind
refactorArgKind =
  try (Position <$> position)
    <|> try (Idx <$> integer)
    <|> try (Flag <$> bool)
    <|> try (Name <$> anyIdentifier)
    <|> try (IdxList <$> integerList)
    <|> (Expr <$> between (symbol "`") (symbol "`") term)

-- | Parse a term from a string.
parseRefactorArgs :: String -> Either String RefactorArgs
parseRefactorArgs contents = case runParser (refactorArgs <* eof) initialParserState "" (fromString contents) of
  Left err -> Left $ show err
  Right p -> Right p
