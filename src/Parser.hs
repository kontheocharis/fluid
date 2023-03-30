module Parser where

{- parser implementation taken from original lambaPi paper:
 
https://www.andres-loeh.de/LambdaPi/LambdaPi.hs

-}


import Syntax
import Typecheck

import Data.List
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language

simplyTyped = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                              reservedNames = ["let", "assume", "putStrLn"] })


lambdaPi = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                             reservedNames = ["forall", "let", "assume", "putStrLn", "out"] })


data Stmt i tinf = Let String i           --  let x = t
                 | Assume [(String,tinf)] --  assume x :: t, assume x :: *
                 | Eval i
                 | PutStrLn String        --  lhs2TeX hacking, allow to print "magic" string
                 | Out String             --  more lhs2TeX hacking, allow to print to files
    deriving (Show)

parseBindings :: CharParser () ([String], [Info])
parseBindings = 
                     (let rec :: [String] -> [Info] -> CharParser () ([String], [Info])
                          rec e ts =
                            do
                             (x,t) <- parens lambdaPi
                                        (do
                                           x <- identifier simplyTyped 
                                           reserved simplyTyped "::"
                                           t <- pInfo
                                           return (x,t))
                             (rec (x : e) (t : ts) <|> return (x : e, t : ts))
                      in rec [] [])
                     <|>
                     do  x <- identifier simplyTyped 
                         reserved simplyTyped "::"
                         t <- pInfo
                         return ([x], [t])
    where
      pInfo = fmap HasType (parseType 0 []) <|> fmap (const (HasKind Star)) (reserved simplyTyped "*")

parseStmt :: [String] -> CharParser () (Stmt TermInf Info)
parseStmt e =
        do
          reserved simplyTyped "let"
          x <- identifier simplyTyped
          reserved simplyTyped "="
          t <- parseTermInf 0 e
          return (Let x t)
    <|> do
          reserved simplyTyped "assume"
          (xs, ts) <- parseBindings
          return (Assume (reverse (zip xs ts)))
    <|> do
          reserved simplyTyped "putStrLn"
          x <- stringLiteral simplyTyped
          return (PutStrLn x)
    <|> do
          reserved lambdaPi "out"
          x <- option "" (stringLiteral simplyTyped)
          return (Out x)
    <|> fmap Eval (parseTermInf 0 e)



parseType :: Int -> [String] -> CharParser () Type
parseType 0 e = 
   try
      ( do
            t <- parseType 1 e 
            rest t <|> return t)
 where
   rest t = 
      do 
         reserved simplyTyped "->"
         t' <- parseType 0 e 
         return (Fun t t')
parseType 1 e = 
     do
         x <- identifier simplyTyped 
         return (TFree (Global x))
 <|> parens simplyTyped (parseType 0 e)


parseTermInf :: Int -> [String] -> CharParser () TermInf
parseTermInf 0 e = 
   try (do 
           t <- parseTermInf 1 e 
           return t)
parseTermInf 1 e = 
   try (do
           t <- parseTermInf 2 e
           rest (Inf t) <|> return t)
   <|>
       (do 
           t <- parens simplyTyped (parseLam e) 
           rest t)
  where
    rest t = 
      do
       reserved simplyTyped "::"
       t' <- parseType 0 e 
       return (Ann t t')
parseTermInf 2 e =
        do
          t <- parseTermInf 3 e
          ts <- many (parseTermChk 3 e)
          return (foldl (:@:) t ts)
parseTermInf 3 e =
       do
          x <- identifier simplyTyped
          case findIndex (== x) e of
            Just n  -> return (Bound n)
            Nothing -> return (Free (Global x))
   <|> parens simplyTyped (parseTermInf 0 e)

parseTermChk :: Int -> [String] -> CharParser () TermChk
parseTermChk 0 e =
        parseLam e
    <|> fmap Inf (parseTermInf 0 e)
parseTermChk p e =
        try (parens simplyTyped (parseLam e))
    <|> fmap Inf (parseTermInf p e)

parseLam :: [String] -> CharParser () TermChk
parseLam e =
        do reservedOp simplyTyped "\\"
           xs <- many1 (identifier simplyTyped)
           reservedOp simplyTyped "->"
           t <- parseTermChk 0 (reverse xs ++ e)
           --  reserved simplyTyped "."
           return (iterate Lam t !! length xs)


parse :: String -> CharParser () a -> String -> IO (Maybe a)
parse f p x = case P.parse (p >>= \ x -> eof >> return x) f x of
     Left e -> putStrLn (show e) >> return Nothing
     Right r -> return (Just r)

{-

Concrete syntax for the language:

types:
   a                                 Base type
 | t -> t'                           Function type

terms:
   e :: t                            Annotation
 | x                                 Variable
 | e e'                              Application
 | \x -> e                           Lambda abstraction

values
   n                                 Neutral term
 | \x -> v                           Lambda abstraction
 
neutral terms:
   x                                 Variable
 | n v                               Application

-}

tfree a = TFree (Global a)

{-
parseTFree :: Parser Type
parseTFree 
  = do
       a <- identifier 
       return (TFree (Global a))

parseTFun :: Parser Type
  = do 
       t <- identifier 
       symbol "-"
       symbol ">"
       t' <- identifier
       return (Fun (tfree t) (tfree t'))

parseType :: Parser Type
parseType =  parseTFun ||| parseTFree
-}