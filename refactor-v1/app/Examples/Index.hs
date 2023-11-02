module Examples.Index (indexDecl, allIndexDecls) where

import Lang (Clause (..), Decl (..), Pat (..), Term (..))
import Vars (var)

indexDecl :: Decl
indexDecl =
  Decl
    "index"
    (PiT (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (MaybeT (V (var "t")))))
    [ Clause [WildP, LNilP] MNothing,
      Clause [ZP, LConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      Clause [SP (VP (var "n")), LConsP WildP (VP (var "xs"))] (App (App (Global "index") (V (var "n"))) (V (var "xs")))
    ]

-- | First step: change normal types to dependent types through ornamental relation.
-- Keep the new indices as holes in recursive calls.
indexDeclR1 :: Decl
indexDeclR1 =
  Decl
    "index"
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
    [ Clause [WildP, WildP, WildP, WildP, LNilP] MNothing,
      Clause [WildP, WildP, WildP, FZP, VConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      Clause [WildP, WildP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))] (App (App (App (App (App (Global "index") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs")))
    ]

-- |  Proposition about ornament indices given by the user.
indexP :: Decl
indexP =
  Decl
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
    [ Clause [VP (var "n1"), VP (var "n2")] (EqT (V (var "n1")) (V (var "n2")))
    ]

-- | Second step: case split on indices
indexDeclR2 :: Decl
indexDeclR2 =
  Decl
    "index"
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
    [ Clause [ZP, ZP, WildP, WildP, LNilP] MNothing,
      Clause [ZP, SP (VP (var "i2")), WildP, WildP, LNilP] MNothing,
      Clause [SP (VP (var "i1")), ZP, WildP, WildP, LNilP] MNothing,
      Clause [SP (VP (var "i1")), SP (VP (var "i2")), WildP, WildP, LNilP] MNothing,
      Clause [ZP, ZP, WildP, FZP, VConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      Clause [ZP, SP (VP (var "i2")), WildP, FZP, VConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      Clause [SP (VP (var "i1")), ZP, WildP, FZP, VConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      Clause [SP (VP (var "i1")), SP (VP (var "i2")), WildP, FZP, VConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      Clause
        [ZP, ZP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
      Clause
        [ZP, SP (VP (var "i2")), WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
      Clause
        [SP (VP (var "i1")), ZP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
      Clause
        [SP (VP (var "i1")), SP (VP (var "i2")), WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs")))
    ]

-- | Third step: identify branches that are impossible (we should be able to semi-automate this) based on pattern unification
indexDeclR3 :: Decl
indexDeclR3 =
  Decl
    "index"
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
    [ ImpossibleClause [ZP, ZP, WildP, WildP, LNilP],
      ImpossibleClause [ZP, SP (VP (var "i2")), WildP, WildP, LNilP],
      Clause [SP (VP (var "i1")), ZP, WildP, WildP, LNilP] MNothing,
      ImpossibleClause [SP (VP (var "i1")), SP (VP (var "i2")), WildP, WildP, LNilP],
      ImpossibleClause [ZP, ZP, WildP, FZP, VConsP (VP (var "x")) WildP],
      ImpossibleClause [ZP, SP (VP (var "i2")), WildP, FZP, VConsP (VP (var "x")) WildP],
      ImpossibleClause [SP (VP (var "i1")), ZP, WildP, FZP, VConsP (VP (var "x")) WildP],
      Clause [SP (VP (var "i1")), SP (VP (var "i2")), WildP, FZP, VConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      ImpossibleClause
        [ZP, ZP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))],
      ImpossibleClause
        [ZP, SP (VP (var "i2")), WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))],
      ImpossibleClause
        [SP (VP (var "i1")), ZP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))],
      Clause
        [SP (VP (var "i1")), SP (VP (var "i2")), WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs")))
    ]

-- | Fourth step: collapse impossible branches (not sure how to automatically figure out ordering here)
indexDeclR4 :: Decl
indexDeclR4 =
  Decl
    "index"
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
    [ Clause [SP (VP (var "i1")), ZP, WildP, WildP, LNilP] MNothing,
      ImpossibleClause [WildP, WildP, WildP, WildP, LNilP],
      Clause [SP (VP (var "i1")), SP (VP (var "i2")), WildP, FZP, VConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      ImpossibleClause [WildP, WildP, WildP, FZP, VConsP (VP (var "x")) WildP],
      Clause
        [SP (VP (var "i1")), SP (VP (var "i2")), WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
      ImpossibleClause
        [WildP, WildP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
    ]

-- | Fifth step: the proposition is an equality, so match on it to remove more branches
indexDeclR5 :: Decl
indexDeclR5 =
  Decl
    "index"
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
    [ ImpossibleClause [SP (VP (var "i1")), ZP, ReflP WildP, WildP, LNilP],
      ImpossibleClause [WildP, WildP, WildP, WildP, LNilP],
      Clause [SP (VP (var "i1")), SP (VP (var "i2")), ReflP WildP, FZP, VConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      ImpossibleClause [WildP, WildP, WildP, FZP, VConsP (VP (var "x")) WildP],
      Clause
        [SP (VP (var "i1")), SP (VP (var "i2")), ReflP WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
      ImpossibleClause
        [WildP, WildP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
    ]

-- | Sixth step: collapse again
indexDeclR6 :: Decl
indexDeclR6 =
  Decl
    "index"
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
    [ ImpossibleClause [WildP, WildP, ReflP WildP, WildP, LNilP],
      Clause [SP (VP (var "i1")), SP (VP (var "i2")), ReflP WildP, FZP, VConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      ImpossibleClause [WildP, WildP, WildP, FZP, VConsP (VP (var "x")) WildP],
      Clause
        [SP (VP (var "i1")), SP (VP (var "i2")), ReflP WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (Hole (var "1"))) (Hole (var "2"))) (Hole (var "3"))) (V (var "n"))) (V (var "xs"))),
      ImpossibleClause
        [WildP, WildP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
    ]

-- | Seventh step: ask user to fill in holes or do it automatically.
-- The recursive proof for this example should be reflexivity purely through unification, but other times it will be harder.
indexDeclR7 :: Decl
indexDeclR7 =
  Decl
    "index"
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
    [ ImpossibleClause [WildP, WildP, ReflP WildP, WildP, LNilP],
      Clause [SP WildP, SP WildP, ReflP WildP, FZP, VConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      ImpossibleClause [WildP, WildP, WildP, FZP, VConsP (VP (var "x")) WildP],
      Clause
        [SP (VP (var "i1")), SP (VP (var "i2")), ReflP WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (V (var "i1"))) (V (var "i2"))) (Refl (V (var "i1")))) (V (var "n"))) (V (var "xs"))),
      ImpossibleClause
        [WildP, WildP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
    ]

-- | Eighth step: realise that im(index) is isomorphic to t, so remove Maybe.
indexDeclR8 :: Decl
indexDeclR8 =
  Decl
    "index"
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
    [ ImpossibleClause [WildP, WildP, ReflP WildP, WildP, LNilP],
      Clause [SP WildP, SP WildP, ReflP WildP, FZP, VConsP (VP (var "x")) WildP] (V (var "x")),
      ImpossibleClause [WildP, WildP, WildP, FZP, VConsP (VP (var "x")) WildP],
      Clause
        [SP (VP (var "i1")), SP (VP (var "i2")), ReflP WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (V (var "i1"))) (V (var "i2"))) (Refl (V (var "i1")))) (V (var "n"))) (V (var "xs"))),
      ImpossibleClause
        [WildP, WildP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
    ]

-- | Ninth step: realise that since the proposition indexP is equality, the two indices can be syntactically unified.
indexDeclR9 :: Decl
indexDeclR9 =
  Decl
    "index"
    ( PiT
        (var "n")
        NatT
        (PiT (var "i") (FinT (V (var "n"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n"))) (V (var "t"))))
    )
    [ ImpossibleClause [WildP, WildP, LNilP],
      Clause [SP WildP, FZP, VConsP (VP (var "x")) WildP] (V (var "x")),
      ImpossibleClause [WildP, FZP, VConsP (VP (var "x")) WildP],
      Clause
        [SP (VP (var "i")), FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (Global "index") (V (var "i"))) (V (var "n"))) (V (var "xs"))),
      ImpossibleClause
        [WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
    ]

-- | Tenth step: The final dependent index function, where we assume the typechecker is able to automatically fill all impossibilities.
indexDepDecl :: Decl
indexDepDecl =
  Decl
    "index"
    (PiT (var "n") NatT (PiT (var "i") (FinT (V (var "n"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n"))) (V (var "t")))))
    [ Clause [WildP, FZP, LConsP (VP (var "x")) WildP] (V (var "x")),
      Clause [SP (VP (var "i")), FSP (VP (var "n")), LConsP WildP (VP (var "xs"))] (App (App (App (Global "indexDep") (V (var "i"))) (V (var "n"))) (V (var "xs")))
    ]

allIndexDecls :: [Decl]
allIndexDecls = [indexDecl, indexDeclR1, indexP, indexDeclR2, indexDeclR3, indexDeclR4, indexDeclR5, indexDeclR6, indexDeclR7, indexDeclR8, indexDeclR9, indexDepDecl]
