module Main (main) where

import Clauses (expandDeclFully)
import Drop (dropDecl)
import Index (indexDecl)
import Lang (Program (..))
import Ornamenting (ornamentDecl)

main :: IO ()
main = ret
  where
    (dropOrn, dropOrnIndices) = ornamentDecl dropDecl
    (indexOrn, indexOrnIndices) = ornamentDecl indexDecl
    indexExpanded = expandDeclFully indexOrn
    dropExpanded = expandDeclFully dropOrn
    ret =
      print $
        Program
          [ dropDecl,
            indexDecl,
            dropOrn,
            indexOrn,
            dropOrnIndices,
            indexOrnIndices,
            indexExpanded,
            dropExpanded
          ]
