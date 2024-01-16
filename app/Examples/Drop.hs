module Examples.Drop (dropDecl) where

import Checking.Vars (var)
import Lang (Clause (..), DeclItem (..), Item (..), Pat (..), Term (..))

-- | The non-dependent drop function.
dropDecl :: Item
dropDecl =
  Decl
    ( DeclItem
        "drop"
        (PiT (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (ListT (V (var "t")))))
        [ Clause [ZP, (VP (var "xs"))] (V (var "xs")),
          Clause [SP (VP (var "i")), LNilP] LNil,
          Clause [SP (VP (var "i")), LConsP WildP (VP (var "xs"))] (App (App (Global "drop") (V (var "i"))) (V (var "xs")))
        ]
    )
