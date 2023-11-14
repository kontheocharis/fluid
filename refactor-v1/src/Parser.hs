module Parser (program, term, pat, decl, initialParserState) where

import Control.Monad.Identity (Identity)
import Control.Monad.State (MonadState (..), State)
import Data.Text (Text)
import GHC.Read (paren)
import Lang (Clause (..), Decl (Decl), Pat (..), Program (..), Term (..), Type, Var (..))
import Text.Parsec (Parsec, ParsecT, char, choice, getState, many, many1, option, optionMaybe, optional, putState, string, (<|>))
import Text.Parsec.Char (alphaNum, letter, oneOf)
import Text.Parsec.Language (emptyDef)
import Text.Parsec.Prim (try)
import Text.Parsec.Text ()
import Text.Parsec.Token (GenLanguageDef (..), GenTokenParser, makeTokenParser)
import qualified Text.ParserCombinators.Parsec.Token as Token

newtype ParserState = ParserState
  { varCount :: Int
  }

initialParserState :: ParserState
initialParserState =
  ParserState
    { varCount = 0
    }

newVarIndex :: Parser Int
newVarIndex = do
  s <- getState
  let i = varCount s
  putState s {varCount = i + 1}
  return i

type Parser a = Parsec Text ParserState a

languageDef :: GenLanguageDef Text ParserState Identity
languageDef =
  emptyDef
    { commentStart = "",
      commentEnd = "",
      commentLine = "--",
      nestedComments = False,
      identStart = letter <|> char '_',
      identLetter = alphaNum <|> char '_' <|> char '\'',
      opStart = oneOf "=-*?\\:[",
      opLetter = oneOf "=->*\\?:[]",
      reservedNames = ["impossible"],
      reservedOpNames = ["->", ":", "=", "**", "\\", "?", ",", "[]", "::"],
      caseSensitive = True
    }

lexer :: GenTokenParser Text ParserState Identity
lexer = makeTokenParser languageDef

parens :: Parser a -> Parser a
parens = Token.parens lexer

identifier :: Parser String
identifier = Token.identifier lexer

symbol :: String -> Parser String
symbol = Token.symbol lexer

reserved :: String -> Parser ()
reserved = Token.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer

comma :: Parser String
comma = Token.comma lexer

colon :: Parser String
colon = Token.colon lexer

program :: Parser Program
program = Program <$> many decl

declSignature :: Parser (String, Type)
declSignature = do
  name <- identifier
  ty <- term
  return (name, ty)

declClause :: String -> Parser Clause
declClause name = do
  _ <- symbol name
  ps <- many pat
  im <- optionMaybe $ reserved "impossible"
  case im of
    Just _ -> return $ ImpossibleClause ps
    Nothing -> do
      reservedOp "="
      Clause ps <$> term

decl :: Parser Decl
decl = do
  (name, ty) <- declSignature
  clauses <- many1 (declClause name)
  return $ Decl name ty clauses

term :: Parser Term
term = choice [lam, piTOrSigmaT, appOrEqTOrCons]

singleTerm :: Parser Term
singleTerm = choice [varOrHole, nil, pair, parens term]

pat :: Parser Pat
pat = error "TODO"

var :: Parser Var
var = try $ do
  name <- identifier
  Var name <$> newVarIndex

freshVar :: Parser Var
freshVar = try $ do
  idx <- newVarIndex
  return $ Var ("n" ++ show idx) idx

named :: Parser (Var, Type)
named =
  ( try . parens $
      do
        optName <- optionMaybe $ do
          name <- var
          _ <- colon
          return name
        ty <- term
        actualName <- maybe freshVar return optName
        return (actualName, ty)
  )
    <|> try
      ( do
          name <- freshVar
          ty <- singleTerm
          return (name, ty)
      )

piTOrSigmaT :: Parser Type
piTOrSigmaT = try $ do
  (name, ty1) <- named
  (reservedOp "->" >> PiT name ty1 <$> term)
    <|> (reservedOp "**" >> SigmaT name ty1 <$> term)

app :: Parser Term
app = do
  ts <- many1 singleTerm
  return $ foldl1 App ts

appOrEqTOrCons :: Parser Term
appOrEqTOrCons = do
  t1 <- app
  (reservedOp "=" >> EqT t1 <$> term) <|> (reservedOp "::" >> LCons t1 <$> term) <|> return t1

lam :: Parser Term
lam = try $ do
  reservedOp "\\"
  v <- var
  reservedOp "->"
  Lam v <$> term

pair :: Parser Term
pair = try . parens $ do
  t1 <- term
  _ <- comma
  Pair t1 <$> term

varOrHole :: Parser Term
varOrHole = try $ do
  hole <- optionMaybe $ reservedOp "?"
  v <- var
  case hole of
    Just _ -> return $ Hole v
    Nothing -> return $ V v

eqT :: Parser Type
eqT = do
  t1 <- term
  reservedOp "="
  EqT t1 <$> term

nil :: Parser Term
nil = do
  reservedOp "[]"
  return LNil
