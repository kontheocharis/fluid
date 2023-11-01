module Main (main) where

import Drop (dropDecl)
import Index (indexDecl)
import Lang (Program (..))
import Ornamenting (ornamentDecl)

main :: IO ()
main = print $ Program ((dropDecl : ornamentDecl dropDecl) ++ (indexDecl : ornamentDecl indexDecl))
