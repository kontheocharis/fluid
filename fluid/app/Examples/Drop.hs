module Examples.Drop () where

import Checking.Vars (var)
import Lang (Clause (..), DeclItem (..), Item (..), Pat (..), PiMode (Explicit), Term (..))

-- | The non-dependent drop function.
-- dropDecl :: Item
-- dropDecl =
--   Decl
--     ( DeclItem
--         "drop"
--         (PiT Explicit (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (ListT (V (var "t")))))
--         [ Clause [(Explicit, ZP), (VP (var "xs"))] (V (var "xs")),
--           Clause [(Explicit, SP) (VP (var "i")), LNilP] LNil,
--           Clause [SP (VP (var "i")), LConsP WildP (VP (var "xs"))] (App (App (Global "drop") (V (var "i"))) (V (var "xs")))
--         ]
--     )
