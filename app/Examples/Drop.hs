module Examples.Drop (dropDecl) where

import Checking.Vars (var)
import Lang (Clause (..), DeclItem (..), Item (..), Term (..))

-- | The non-dependent drop function.
dropDecl :: Item
dropDecl =
  Decl
    ( DeclItem
        "drop"
        (PiT (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (ListT (V (var "t")))))
        [ Clause [Z, (V (var "xs"))] (V (var "xs")),
          Clause [S (V (var "i")), LNil] LNil,
          Clause [S (V (var "i")), LCons Wild (V (var "xs"))] (App (App (Global "drop") (V (var "i"))) (V (var "xs")))
        ]
    )
