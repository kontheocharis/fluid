module RefacChgParam where

import Utils

import REPL

import Syntax
import Eval
import Typecheck
-- import LambdaPi.Quote
import Parser
import Pretty

import Text.PrettyPrint.HughesPJ hiding (parens)

refacChgParam :: String -> IO ()
refacChgParam f = do
    (x,y,z) <- typecheck f 
    putStrLn $ concat (map showNameValue y)