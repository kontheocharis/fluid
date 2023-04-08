module Pretty where

import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language

import Syntax


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
--iPrint_ p ii (Nil a)    = iPrint_ p ii (Free (Global "Nil") :@: a)
--iPrint_ p ii (Cons a n x xs) =
--                             iPrint_ p ii (Free (Global "Cons") :@: a :@: n :@: x :@: xs)
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
cPrint_ p ii (Nil a)    = iPrint_ p ii (Free (Global "Nil") :@: a)
cPrint_ p ii (Cons a n x xs) =
                             iPrint_ p ii (Free (Global "Cons") :@: a :@: n :@: x :@: xs)
--  cPrint_ p ii (Refl_ a x) = iPrint_ p ii (Free_ (Global "Refl") :$: a :$: x)
--  cPrint_ p ii (FZero_ n)  = iPrint_ p ii (Free_ (Global "FZero") :$: n)
--  cPrint_ p ii (FSucc_ n f)= iPrint_ p ii (Free_ (Global "FSucc") :$: n :$: f)

fromNat_ :: Int -> Int -> TermChk -> Doc
fromNat_ n ii Zero = int n
fromNat_ n ii (Succ k) = fromNat_ (n + 1) ii k
fromNat_ n ii t = parensIf True (int n PP.<> text " + " PP.<> cPrint_ 0 ii t)

print = render . cPrint_ 0 0
