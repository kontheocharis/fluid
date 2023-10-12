module Main (main) where

import Lang
  ( Clause (..),
    Decl (..),
    Pat (..),
    Program (Program),
    Term (..),
  )
import Vars (var)

-- | The non-dependent index function.
indexDecl :: Decl
indexDecl =
  Decl
    "index"
    (PiT (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (MaybeT (V (var "t")))))
    [ Clause [WildP, LNilP] MNothing,
      Clause [ZP, LConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      Clause [SP (VP (var "n")), LConsP WildP (VP (var "xs"))] (App (App (Global "index") (V (var "n"))) (V (var "xs")))
    ]

-- | The dependent index function.
indexDepDecl :: Decl
indexDepDecl =
  Decl
    "indexDep"
    (PiT (var "n") NatT (PiT (var "i") (FinT (V (var "n"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n"))) (V (var "t")))))
    [ ImpossibleClause [WildP, LNilP],
      Clause [FZP, LConsP (VP (var "x")) WildP] (V (var "x")),
      Clause [FSP (VP (var "n")), LConsP WildP (VP (var "xs"))] (App (App (Global "indexDep") (V (var "n"))) (V (var "xs")))
    ]

transform :: Decl -> Decl
transform _ = error "TODO: implement refactoring"

-- we need to get to the point: `transform indexDecl = indexDepDecl`

main :: IO ()
main = print $ Program [indexDecl, indexDepDecl]
