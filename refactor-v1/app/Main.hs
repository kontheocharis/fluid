module Main (main) where

import Lang
  ( Clause (..),
    Decl (..),
    Pat (..),
    Term (..),
  )
import Vars (var)

indexDecl :: Decl
indexDecl =
  Decl
    "index"
    (PiT (var "n") NatT (PiT (var "l") (ListT (V (var "t"))) (MaybeT (V (var "t")))))
    [ Clause [WildP, LNilP] MNothing,
      Clause [ZP, LConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      Clause [SP (VP (var "n")), LConsP WildP (VP (var "xs"))] (App (App (Global "index") (V (var "n"))) (V (var "xs")))
    ]

main :: IO ()
main = print indexDecl
