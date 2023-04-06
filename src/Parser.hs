module Parser where

{- parser implementation taken from original lambaPi paper:
 
https://www.andres-loeh.de/LambdaPi/LambdaPi.hs

-}
-- import Prelude hiding (<>)

import Syntax
import Typecheck

import Data.List
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP
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


toNat_ :: Integer -> TermInf
toNat_ n = Ann (toNat_' n) (Inf Nat)

toNat_' :: Integer -> TermChk
toNat_' 0  =  Zero
toNat_' n  =  Succ ((toNat_' (n - 1)))



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
    <|> do
          n <- natural lambdaPi
          return (toNat_ n)
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


--- pretty print
parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id

nestedForall_ :: Int -> [(Int, TermChk)] -> TermChk -> Doc
nestedForall_ ii ds (Inf (Pi d r)) = nestedForall_ (ii + 1) ((ii, d) : ds) r
nestedForall_ ii ds x              = sep [text "forall " PP.<> sep [parensIf True (text (vars !! n) PP.<> text " :: " PP.<> cPrint_ 0 n d) | (n,d) <- reverse ds] PP.<> text " .", cPrint_ 0 ii x]

vars :: [String]
vars = [ c : n | n <- "" : map show [1..], c <- ['x','y','z'] ++ ['a'..'w'] ]

iPrint_ :: Int -> Int -> TermInf -> Doc
iPrint_ p ii (Ann c ty)       =  parensIf (p > 1) (cPrint_ 2 ii c PP.<> text " :: " PP.<> cPrint_ 0 ii ty)
iPrint_ p ii Star             =  text "*"
iPrint_ p ii (Pi d (Inf (Pi d' r)))
                                 =  parensIf (p > 0) (nestedForall_ (ii + 2) [(ii + 1, d'), (ii, d)] r)
iPrint_ p ii (Pi d r)         =  parensIf (p > 0) (sep [text "forall " PP.<> text (vars !! ii) PP.<> text " :: " PP.<> cPrint_ 0 ii d PP.<> text " .", cPrint_ 0 (ii + 1) r])
iPrint_ p ii (Bound k)        =  text (vars !! (ii - k - 1))
iPrint_ p ii (Free (Global s))=  text s
iPrint_ p ii (i :@: c)         =  parensIf (p > 2) (sep [iPrint_ 2 ii i, nest 2 (cPrint_ 3 ii c)])
iPrint_ p ii Nat              =  text "Nat"
iPrint_ p ii (NatElim m z s n)=  iPrint_ p ii (Free (Global "natElim") :@: m :@: z :@: s :@: n)
iPrint_ p ii (Vec a n)        =  iPrint_ p ii (Free (Global "Vec") :@: a :@: n)
iPrint_ p ii (VecElim a m mn mc n xs)
                                 =  iPrint_ p ii (Free (Global "vecElim") :@: a :@: m :@: mn :@: mc :@: n :@: xs)
iPrint_ p ii (Nil a)    = iPrint_ p ii (Free (Global "Nil") :@: a)
iPrint_ p ii (Cons a n x xs) =
                             iPrint_ p ii (Free (Global "Cons") :@: a :@: n :@: x :@: xs)
-- iPrint_ p ii (Eq_ a x y)       =  iPrint_ p ii (Free_ (Global "Eq") :$: a :$: x :$: y)
-- iPrint_ p ii (EqElim_ a m mr x y eq)
--                                 =  iPrint_ p ii (Free_ (Global "eqElim") :$: a :$: m :$: mr :$: x :$: y :$: eq)
-- iPrint_ p ii (Fin_ n)          =  iPrint_ p ii (Free_ (Global "Fin") :$: n)
-- iPrint_ p ii (FinElim_ m mz ms n f)
--                                 =  iPrint_ p ii (Free_ (Global "finElim") :$: m :$: mz :$: ms :$: n :$: f)
iPrint_ p ii x                 =  text ("[" ++ show x ++ "]")

cPrint_ :: Int -> Int -> TermChk -> Doc
cPrint_ p ii (Inf i)    = iPrint_ p ii i
cPrint_ p ii (Lam c)    = parensIf (p > 0) (text "\\ " PP.<> text (vars !! ii) PP.<> text " -> " PP.<> cPrint_ 0 (ii + 1) c)
cPrint_ p ii Zero       = fromNat_ 0 ii Zero     --  text "Zero"
cPrint_ p ii (Succ n)   = fromNat_ 0 ii (Succ n) --  iPrint_ p ii (Free_ (Global "Succ") :$: n)
-- cPrint_ p ii (Nil_ a)    = iPrint_ p ii (Free_ (Global "Nil") :$: a)
-- cPrint_ p ii (Cons_ a n x xs) =
--                             iPrint_ p ii (Free_ (Global "Cons") :$: a :$: n :$: x :$: xs)
--  cPrint_ p ii (Refl_ a x) = iPrint_ p ii (Free_ (Global "Refl") :$: a :$: x)
--  cPrint_ p ii (FZero_ n)  = iPrint_ p ii (Free_ (Global "FZero") :$: n)
--  cPrint_ p ii (FSucc_ n f)= iPrint_ p ii (Free_ (Global "FSucc") :$: n :$: f)

fromNat_ :: Int -> Int -> TermChk -> Doc
fromNat_ n ii Zero = int n
fromNat_ n ii (Succ k) = fromNat_ (n + 1) ii k
fromNat_ n ii t = parensIf True (int n PP.<> text " + " PP.<> cPrint_ 0 ii t)

print = render . cPrint_ 0 0
