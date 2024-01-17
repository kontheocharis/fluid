module Examples.Index (indexDecl, allIndexDecls) where

import Checking.Vars (var)
import Lang (Clause (..), DeclItem (..), Item (..), Term (..))

indexDecl :: Item
indexDecl =
  Decl $
    DeclItem
      "indexP"
      (PiT (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (MaybeT (V (var "t")))))
      [ Clause [Wild, LNil] MNothing,
        Clause [Z, LCons (V (var "x")) Wild] (MJust (V (var "x"))),
        Clause [S (V (var "n")), LCons Wild (V (var "xs"))] (App (App (Global "indexP") (V (var "n"))) (V (var "xs")))
      ]

-- | First step: change normal types to dependent types through ornamental relation.
-- Keep the new indices as holes in recursive calls.
indexDeclR1 :: Item
indexDeclR1 =
  Decl $
    DeclItem
      "indexP"
      ( PiT
          (var "n1")
          NatT
          ( PiT
              (var "n2")
              NatT
              ( PiT
                  (var "prf")
                  (App (App (Global "indexP") (V (var "n1"))) (V (var "n2")))
                  (PiT (var "i") (FinT (V (var "n1"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n2"))) (MaybeT (V (var "t")))))
              )
          )
      )
      [ Clause [Wild, Wild, Wild, Wild, LNil] MNothing,
        Clause [Wild, Wild, Wild, FZ, VCons (V (var "x")) Wild] (MJust (V (var "x"))),
        Clause [Wild, Wild, Wild, FS (V (var "n")), VCons Wild (V (var "xs"))] (App (App (App (App (App (Global "indexP") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs")))
      ]

-- |  Proposition about ornament indices given by the user.
indexP :: Item
indexP =
  Decl $
    DeclItem
      "indexP"
      ( PiT
          (var "n1")
          NatT
          ( PiT
              (var "n2")
              NatT
              TyT
          )
      )
      [ Clause [V (var "n1"), V (var "n2")] (EqT (V (var "n1")) (V (var "n2")))
      ]

-- | Second step: case split on indices
indexDeclR2 :: Item
indexDeclR2 =
  Decl $
    DeclItem
      "indexP"
      ( PiT
          (var "n1")
          NatT
          ( PiT
              (var "n2")
              NatT
              ( PiT
                  (var "prf")
                  (App (App (Global "indexP") (V (var "n1"))) (V (var "n2")))
                  (PiT (var "i") (FinT (V (var "n1"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n2"))) (MaybeT (V (var "t")))))
              )
          )
      )
      [ Clause [Z, Z, Wild, Wild, LNil] MNothing,
        Clause [Z, S (V (var "i2")), Wild, Wild, LNil] MNothing,
        Clause [S (V (var "i1")), Z, Wild, Wild, LNil] MNothing,
        Clause [S (V (var "i1")), S (V (var "i2")), Wild, Wild, LNil] MNothing,
        Clause [Z, Z, Wild, FZ, VCons (V (var "x")) Wild] (MJust (V (var "x"))),
        Clause [Z, S (V (var "i2")), Wild, FZ, VCons (V (var "x")) Wild] (MJust (V (var "x"))),
        Clause [S (V (var "i1")), Z, Wild, FZ, VCons (V (var "x")) Wild] (MJust (V (var "x"))),
        Clause [S (V (var "i1")), S (V (var "i2")), Wild, FZ, VCons (V (var "x")) Wild] (MJust (V (var "x"))),
        Clause
          [Z, Z, Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
          (App (App (App (App (App (Global "indexP") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
        Clause
          [Z, S (V (var "i2")), Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
          (App (App (App (App (App (Global "indexP") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
        Clause
          [S (V (var "i1")), Z, Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
          (App (App (App (App (App (Global "indexP") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
        Clause
          [S (V (var "i1")), S (V (var "i2")), Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
          (App (App (App (App (App (Global "indexP") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs")))
      ]

-- | Third step: identify branches that are impossible (we should be able to semi-automate this) based on pattern unification
indexDeclR3 :: Item
indexDeclR3 =
  Decl $
    DeclItem
      "indexP"
      ( PiT
          (var "n1")
          NatT
          ( PiT
              (var "n2")
              NatT
              ( PiT
                  (var "prf")
                  (App (App (Global "indexP") (V (var "n1"))) (V (var "n2")))
                  (PiT (var "i") (FinT (V (var "n1"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n2"))) (MaybeT (V (var "t")))))
              )
          )
      )
      [ ImpossibleClause [Z, Z, Wild, Wild, LNil],
        ImpossibleClause [Z, S (V (var "i2")), Wild, Wild, LNil],
        Clause [S (V (var "i1")), Z, Wild, Wild, LNil] MNothing,
        ImpossibleClause [S (V (var "i1")), S (V (var "i2")), Wild, Wild, LNil],
        ImpossibleClause [Z, Z, Wild, FZ, VCons (V (var "x")) Wild],
        ImpossibleClause [Z, S (V (var "i2")), Wild, FZ, VCons (V (var "x")) Wild],
        ImpossibleClause [S (V (var "i1")), Z, Wild, FZ, VCons (V (var "x")) Wild],
        Clause [S (V (var "i1")), S (V (var "i2")), Wild, FZ, VCons (V (var "x")) Wild] (MJust (V (var "x"))),
        ImpossibleClause
          [Z, Z, Wild, FS (V (var "n")), VCons Wild (V (var "xs"))],
        ImpossibleClause
          [Z, S (V (var "i2")), Wild, FS (V (var "n")), VCons Wild (V (var "xs"))],
        ImpossibleClause
          [S (V (var "i1")), Z, Wild, FS (V (var "n")), VCons Wild (V (var "xs"))],
        Clause
          [S (V (var "i1")), S (V (var "i2")), Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
          (App (App (App (App (App (Global "indexP") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs")))
      ]

-- | Fourth step: collapse impossible branches (not sure how to automatically figure out ordering here)
indexDeclR4 :: Item
indexDeclR4 =
  Decl $
    DeclItem
      "indexP"
      ( PiT
          (var "n1")
          NatT
          ( PiT
              (var "n2")
              NatT
              ( PiT
                  (var "prf")
                  (App (App (Global "indexP") (V (var "n1"))) (V (var "n2")))
                  (PiT (var "i") (FinT (V (var "n1"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n2"))) (MaybeT (V (var "t")))))
              )
          )
      )
      [ Clause [S (V (var "i1")), Z, Wild, Wild, LNil] MNothing,
        ImpossibleClause [Wild, Wild, Wild, Wild, LNil],
        Clause [S (V (var "i1")), S (V (var "i2")), Wild, FZ, VCons (V (var "x")) Wild] (MJust (V (var "x"))),
        ImpossibleClause [Wild, Wild, Wild, FZ, VCons (V (var "x")) Wild],
        Clause
          [S (V (var "i1")), S (V (var "i2")), Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
          (App (App (App (App (App (Global "indexP") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
        ImpossibleClause
          [Wild, Wild, Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
      ]

-- | Fifth step: the proposition is an equality, so match on it to remove more branches
indexDeclR5 :: Item
indexDeclR5 =
  Decl $
    DeclItem
      "indexP"
      ( PiT
          (var "n1")
          NatT
          ( PiT
              (var "n2")
              NatT
              ( PiT
                  (var "prf")
                  (App (App (Global "indexP") (V (var "n1"))) (V (var "n2")))
                  (PiT (var "i") (FinT (V (var "n1"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n2"))) (MaybeT (V (var "t")))))
              )
          )
      )
      [ ImpossibleClause [S (V (var "i1")), Z, Refl Wild, Wild, LNil],
        ImpossibleClause [Wild, Wild, Wild, Wild, LNil],
        Clause [S (V (var "i1")), S (V (var "i2")), Refl Wild, FZ, VCons (V (var "x")) Wild] (MJust (V (var "x"))),
        ImpossibleClause [Wild, Wild, Wild, FZ, VCons (V (var "x")) Wild],
        Clause
          [S (V (var "i1")), S (V (var "i2")), Refl Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
          (App (App (App (App (App (Global "indexP") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
        ImpossibleClause
          [Wild, Wild, Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
      ]

-- | Sixth step: collapse again
indexDeclR6 :: Item
indexDeclR6 =
  Decl $
    DeclItem
      "indexP"
      ( PiT
          (var "n1")
          NatT
          ( PiT
              (var "n2")
              NatT
              ( PiT
                  (var "prf")
                  (App (App (Global "indexP") (V (var "n1"))) (V (var "n2")))
                  (PiT (var "i") (FinT (V (var "n1"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n2"))) (MaybeT (V (var "t")))))
              )
          )
      )
      [ ImpossibleClause [Wild, Wild, Refl Wild, Wild, LNil],
        Clause [S (V (var "i1")), S (V (var "i2")), Refl Wild, FZ, VCons (V (var "x")) Wild] (MJust (V (var "x"))),
        ImpossibleClause [Wild, Wild, Wild, FZ, VCons (V (var "x")) Wild],
        Clause
          [S (V (var "i1")), S (V (var "i2")), Refl Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
          (App (App (App (App (App (Global "indexP") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
        ImpossibleClause
          [Wild, Wild, Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
      ]

-- | Seventh step: ask user to fill in holes or do it automatically.
-- The recursive proof for this example should be reflexivity purely through unification, but other times it will be harder.
indexDeclR7 :: Item
indexDeclR7 =
  Decl $
    DeclItem
      "indexP"
      ( PiT
          (var "n1")
          NatT
          ( PiT
              (var "n2")
              NatT
              ( PiT
                  (var "prf")
                  (App (App (Global "indexP") (V (var "n1"))) (V (var "n2")))
                  (PiT (var "i") (FinT (V (var "n1"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n2"))) (MaybeT (V (var "t")))))
              )
          )
      )
      [ ImpossibleClause [Wild, Wild, Refl Wild, Wild, LNil],
        Clause [S Wild, S Wild, Refl Wild, FZ, VCons (V (var "x")) Wild] (MJust (V (var "x"))),
        ImpossibleClause [Wild, Wild, Wild, FZ, VCons (V (var "x")) Wild],
        Clause
          [S (V (var "i1")), S (V (var "i2")), Refl Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
          (App (App (App (App (App (Global "indexP") (V (var "i1"))) (V (var "i2"))) (Refl (V (var "i1")))) (V (var "n"))) (V (var "xs"))),
        ImpossibleClause
          [Wild, Wild, Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
      ]

-- | Eighth step: realise that im(index) is isomorphic to t, so remove Maybe.
indexDeclR8 :: Item
indexDeclR8 =
  Decl $
    DeclItem
      "indexP"
      ( PiT
          (var "n1")
          NatT
          ( PiT
              (var "n2")
              NatT
              ( PiT
                  (var "prf")
                  (App (App (Global "indexP") (V (var "n1"))) (V (var "n2")))
                  (PiT (var "i") (FinT (V (var "n1"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n2"))) (V (var "t"))))
              )
          )
      )
      [ ImpossibleClause [Wild, Wild, Refl Wild, Wild, LNil],
        Clause [S Wild, S Wild, Refl Wild, FZ, VCons (V (var "x")) Wild] (V (var "x")),
        ImpossibleClause [Wild, Wild, Wild, FZ, VCons (V (var "x")) Wild],
        Clause
          [S (V (var "i1")), S (V (var "i2")), Refl Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
          (App (App (App (App (App (Global "indexP") (V (var "i1"))) (V (var "i2"))) (Refl (V (var "i1")))) (V (var "n"))) (V (var "xs"))),
        ImpossibleClause
          [Wild, Wild, Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
      ]

-- | Ninth step: realise that since the proposition index is equality, the two indices can be syntactically unified.
indexDeclR9 :: Item
indexDeclR9 =
  Decl $
    DeclItem
      "indexP"
      ( PiT
          (var "n")
          NatT
          (PiT (var "i") (FinT (V (var "n"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n"))) (V (var "t"))))
      )
      [ ImpossibleClause [Wild, Wild, LNil],
        Clause [S Wild, FZ, VCons (V (var "x")) Wild] (V (var "x")),
        ImpossibleClause [Wild, FZ, VCons (V (var "x")) Wild],
        Clause
          [S (V (var "i")), FS (V (var "n")), VCons Wild (V (var "xs"))]
          (App (App (App (Global "indexP") (V (var "i"))) (V (var "n"))) (V (var "xs"))),
        ImpossibleClause
          [Wild, FS (V (var "n")), VCons Wild (V (var "xs"))]
      ]

-- | Tenth step: The final dependent index function, where we assume the typechecker is able to automatically fill all impossibilities.
indexDepDecl :: Item
indexDepDecl =
  Decl $
    DeclItem
      "indexP"
      (PiT (var "n") NatT (PiT (var "i") (FinT (V (var "n"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n"))) (V (var "t")))))
      [ Clause [Wild, FZ, LCons (V (var "x")) Wild] (V (var "x")),
        Clause [S (V (var "i")), FS (V (var "n")), LCons Wild (V (var "xs"))] (App (App (App (Global "indexDep") (V (var "i"))) (V (var "n"))) (V (var "xs")))
      ]

allIndexDecls :: [Item]
allIndexDecls =
  [ indexDecl,
    indexDeclR1,
    indexP,
    indexDeclR2,
    indexDeclR3,
    indexDeclR4,
    indexDeclR5,
    indexDeclR6,
    indexDeclR7,
    indexDeclR8,
    indexDeclR9,
    indexDepDecl
  ]
