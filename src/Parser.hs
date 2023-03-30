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

{-
toNat_ :: Integer -> TermInf
toNat_ n = Ann (toNat_' n) (Inf Nat)

toNat_' :: Integer -> TermChk
toNat_' 0  =  Zero
toNat_' n  =  Succ (toNat_' (n - 1))
-}


parseStmt_ :: [String] -> CharParser () (Stmt TermInf TermChk)
parseStmt_ e =
        do
          reserved lambdaPi "let"
          x <- identifier lambdaPi
          reserved lambdaPi "="
          t <- parseITerm_ 0 e
          return (Let x t)
    <|> do
          reserved lambdaPi "assume"
          (xs, ts) <- parseBindings_ False [] 
          return (Assume (reverse (zip xs ts)))
    <|> do
          reserved lambdaPi "putStrLn"
          x <- stringLiteral lambdaPi
          return (PutStrLn x)
    <|> do
          reserved lambdaPi "out"
          x <- option "" (stringLiteral lambdaPi)
          return (Out x)
    <|> fmap Eval (parseITerm_ 0 e)

parseBindings_ :: Bool -> [String] -> CharParser () ([String], [TermChk])
parseBindings_ b e = 
                     (let rec :: [String] -> [TermChk] -> CharParser () ([String], [TermChk])
                          rec e ts =
                            do
                             (x,t) <- parens lambdaPi
                                        (do
                                           x <- identifier lambdaPi
                                           reserved lambdaPi "::"
                                           t <- parseCTerm_ 0 (if b then e else [])
                                           return (x,t))
                             (rec (x : e) (t : ts) <|> return (x : e, t : ts))
                      in rec e [])
                     <|>
                     do  x <- identifier lambdaPi
                         reserved lambdaPi "::"
                         t <- parseCTerm_ 0 e
                         return (x : e, [t])



parseITerm_ :: Int -> [String] -> CharParser () TermInf
parseITerm_ 0 e =
        do
          reserved lambdaPi "forall"
          (fe,t:ts) <- parseBindings_ True e
          reserved lambdaPi "."
          t' <- parseCTerm_ 0 fe
          return (foldl (\ p t -> Pi t (Inf p)) (Pi t t') ts)
    <|>
    try
       (do
          t <- parseITerm_ 1 e
          rest (Inf t) <|> return t)
    <|> do
          t <- parens lambdaPi (parseLam_ e)
          rest t
    where
      rest t =
        do
          reserved lambdaPi "->"
          t' <- parseCTerm_ 0 ([]:e)
          return (Pi t t')
parseITerm_ 1 e =
    try
       (do
          t <- parseITerm_ 2 e
          rest (Inf t) <|> return t)
    <|> do
          t <- parens lambdaPi (parseLam_ e)
          rest t
    where
      rest t =
        do
          reserved lambdaPi "::"
          t' <- parseCTerm_ 0 e
          return (Ann t t')
parseITerm_ 2 e =
        do
          t <- parseITerm_ 3 e
          ts <- many (parseCTerm_ 3 e)
          return (foldl (:@:) t ts)
parseITerm_ 3 e =
        do
          reserved lambdaPi "*"
          return Star
   {- <|> do
          n <- natural lambdaPi
          return (toNat_ n)
   -}
    <|> do
          x <- identifier lambdaPi
          case findIndex (== x) e of
            Just n  -> return (Bound n)
            Nothing -> return (Free (Global x))
    <|> parens lambdaPi (parseITerm_ 0 e)
  
parseCTerm_ :: Int -> [String] -> CharParser () TermChk
parseCTerm_ 0 e =
        parseLam_ e
    <|> fmap Inf (parseITerm_ 0 e)
parseCTerm_ p e =
        try (parens lambdaPi (parseLam_ e))
    <|> fmap Inf (parseITerm_ p e)
  
parseLam_ :: [String] -> CharParser () TermChk
parseLam_ e =
        do reservedOp lambdaPi "\\"
           xs <- many1 (identifier lambdaPi)
           reservedOp lambdaPi "->"
           t <- parseCTerm_ 0 (reverse xs ++ e)
           --  reserved lambdaPi "."
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

-- tfree a = TFree (Global a)

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