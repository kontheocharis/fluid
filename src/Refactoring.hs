module Refactoring where

import Prelude hiding (print, (<>))
import Control.Monad.Except
import Data.List
import Data.Char
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language
import System.IO hiding (print)
import System.IO.Error


import Syntax
import Typecheck
import Eval
import Parser

parseIt :: String -> IO (Maybe TermChk)
parseIt s = parse "" (parseCTerm_ 0 []) s

changeFirstParam :: [ String ]   -- args
                -> TermChk
                -> TermChk
changeFirstParam args ast = undefined