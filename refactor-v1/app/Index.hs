module Index (indexDecl, allIndexDecls) where

import Lang (Clause (..), Decl (..), Pat (..), Term (..))
import Vars (var)

indexDecl :: Decl
indexDecl =
  Decl
    Nothing
    "index"
    (PiT (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (MaybeT (V (var "t")))))
    [ Clause [WildP, LNilP] MNothing,
      Clause [ZP, LConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      Clause [SP (VP (var "n")), LConsP WildP (VP (var "xs"))] (App (App (Global "index") (V (var "n"))) (V (var "xs")))
    ]

indexDeclR1 :: Decl
indexDeclR1 =
  Decl
    ( Just
        "First step: change normal types to dependent types through ornamental relation.\n\
        \Keep the new indices as holes in recursive calls."
    )
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
      Clause [WildP, WildP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))] (App (App (App (App (App (Global "index") (Hole 1)) (Hole 2)) (Hole 3)) (V (var "n"))) (V (var "xs")))
    ]

indexP :: Decl
indexP =
  Decl
    ( Just
        "Proposition about ornament indices given by the user."
    )
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

indexDeclR2 :: Decl
indexDeclR2 =
  Decl
    (Just "Second step: case split on indices")
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
        (App (App (App (App (App (Global "index") (Hole 1)) (Hole 2)) (Hole 3)) (V (var "n"))) (V (var "xs"))),
      Clause
        [ZP, SP (VP (var "i2")), WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (Hole 1)) (Hole 2)) (Hole 3)) (V (var "n"))) (V (var "xs"))),
      Clause
        [SP (VP (var "i1")), ZP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (Hole 1)) (Hole 2)) (Hole 3)) (V (var "n"))) (V (var "xs"))),
      Clause
        [SP (VP (var "i1")), SP (VP (var "i2")), WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
        (App (App (App (App (App (Global "index") (Hole 1)) (Hole 2)) (Hole 3)) (V (var "n"))) (V (var "xs")))
    ]

indexDeclR3 :: Decl
indexDeclR3 =
  Decl
    (Just "Third step: identify branches that are impossible (we should be able to semi-automate this) based on pattern unification")
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
        (App (App (App (App (App (Global "index") (Hole 1)) (Hole 2)) (Hole 3)) (V (var "n"))) (V (var "xs")))
    ]

indexDeclR4 :: Decl
indexDeclR4 =
  Decl
    (Just "Fourth step: collapse impossible branches (not sure how to automatically figure out ordering here)")
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
        (App (App (App (App (App (Global "index") (Hole 1)) (Hole 2)) (Hole 3)) (V (var "n"))) (V (var "xs"))),
      ImpossibleClause
        [WildP, WildP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
    ]

indexDeclR5 :: Decl
indexDeclR5 =
  Decl
    (Just "Fifth step: the proposition is an equality, so match on it to remove more branches")
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
        (App (App (App (App (App (Global "index") (Hole 1)) (Hole 2)) (Hole 3)) (V (var "n"))) (V (var "xs"))),
      ImpossibleClause
        [WildP, WildP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
    ]

indexDeclR6 :: Decl
indexDeclR6 =
  Decl
    (Just "Sixth step: collapse again")
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
        (App (App (App (App (App (Global "index") (Hole 1)) (Hole 2)) (Hole 3)) (V (var "n"))) (V (var "xs"))),
      ImpossibleClause
        [WildP, WildP, WildP, FSP (VP (var "n")), VConsP WildP (VP (var "xs"))]
    ]

indexDeclR7 :: Decl
indexDeclR7 =
  Decl
    ( Just
        "Seventh step: ask user to fill in holes or do it automatically.\n\
        \The recursive proof for this example should be reflexivity purely through unification, but other times it will be harder."
    )
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

indexDeclR8 :: Decl
indexDeclR8 =
  Decl
    ( Just
        "Eighth step: realise that im(index) is isomorphic to t, so remove Maybe."
    )
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

indexDeclR9 :: Decl
indexDeclR9 =
  Decl
    ( Just
        "Ninth step: realise that since the proposition indexP is equality, the two indices can be syntactically unified."
    )
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

indexDepDecl :: Decl
indexDepDecl =
  Decl
    (Just "Tenth step: The final dependent index function, where we assume the typechecker is able to automatically fill all impossibilities.")
    "index"
    (PiT (var "n") NatT (PiT (var "i") (FinT (V (var "n"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n"))) (V (var "t")))))
    [ Clause [WildP, FZP, LConsP (VP (var "x")) WildP] (V (var "x")),
      Clause [SP (VP (var "i")), FSP (VP (var "n")), LConsP WildP (VP (var "xs"))] (App (App (App (Global "indexDep") (V (var "i"))) (V (var "n"))) (V (var "xs")))
    ]

allIndexDecls :: [Decl]
allIndexDecls = [indexDecl, indexDeclR1, indexP, indexDeclR2, indexDeclR3, indexDeclR4, indexDeclR5, indexDeclR6, indexDeclR7, indexDeclR8, indexDeclR9, indexDepDecl]
