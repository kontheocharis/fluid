module Main (main) where

import Index (allIndexDecls)
import Lang (Program (..))

main :: IO ()
main = print $ Program allIndexDecls
