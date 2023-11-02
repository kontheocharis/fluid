module Main (main) where

import Clauses (expandDeclFully)
import Examples.Drop (dropDecl)
import Examples.Index (indexDecl)
import Lang (Clause (..), Decl (Decl), Pat (..), Program (..), Term (..))
import Ornamenting (ornamentDecl)
import Vars (var)

main :: IO ()
main = ret
  where
    (dropOrn, dropOrnIndices) = ornamentDecl dropDecl
    (indexOrn, indexOrnIndices) = ornamentDecl indexDecl

    identityDecl =
      Decl
        "identity"
        (PiT (var "num") NatT NatT)
        [ Clause [ZP] Z,
          Clause [SP (VP (var "num"))] (S (App (Global "identity") (V (var "num"))))
        ]

    (identityOrn, identityOrnIndices) =
      ornamentDecl identityDecl

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
            dropExpanded,
            identityDecl,
            identityOrn,
            identityOrnIndices
          ]
