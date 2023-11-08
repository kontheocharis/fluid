module Main (main) where

import Checking.Context (emptyTcState)
import Checking.Typechecking (checkProgram, checkTerm, inferTerm, normaliseTermFully, unifyToLeft)
import Checking.Vars (var)
import Control.Monad.State (StateT (runStateT))
import Examples.Drop (dropDecl)
import Examples.Index (indexDecl)
import Lang (Clause (..), Decl (Decl), Pat (..), Program (..), Term (..), Type)
import Refactoring.Clauses (expandDeclFully)
import Refactoring.Ornamenting (ornamentDecl)

testProgram :: Program
testProgram = ret
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

unify :: Term -> Term -> IO ()
unify a b = do
  putStrLn $ "Unifying " ++ show a ++ " and " ++ show b
  case runStateT (unifyToLeft a b) emptyTcState of
    Left err -> putStrLn $ "Error: " ++ show err
    Right (s, _) -> putStrLn $ "Result: " ++ show s

normalise :: Term -> IO ()
normalise a = do
  putStrLn $ "Normalising " ++ show a
  case runStateT (normaliseTermFully a) emptyTcState of
    Left err -> putStrLn $ "Error: " ++ show err
    Right (s, _) -> putStrLn $ "Result: " ++ show s

check :: Term -> Type -> IO ()
check a t = do
  putStrLn $ "Checking " ++ show a ++ " : " ++ show t
  case runStateT (checkTerm a t) emptyTcState of
    Left err -> putStrLn $ "Error: " ++ show err
    Right (s, _) -> putStrLn $ "Valid! Substitutions: " ++ show s

infer :: Term -> IO ()
infer a = do
  putStrLn $ "Inferring " ++ show a
  case runStateT (inferTerm a) emptyTcState of
    Left err -> putStrLn $ "Error: " ++ show err
    Right (s, _) -> putStrLn $ "Result: " ++ show a ++ " : " ++ show s

checkProg :: Program -> IO ()
checkProg p = do
  putStrLn $ "Checking program:\n" ++ show p
  case runStateT (checkProgram p) emptyTcState of
    Left err -> putStrLn $ "Error: " ++ show err
    Right (_, _) -> putStrLn "Valid!"

explicitIndexDecl :: Decl
explicitIndexDecl =
  Decl
    "index"
    (PiT (var "t") TyT (PiT (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (MaybeT (V (var "t"))))))
    [ Clause [WildP, WildP, LNilP] MNothing,
      Clause [WildP, ZP, LConsP (VP (var "x")) WildP] (MJust (V (var "x"))),
      Clause [VP (var "t"), SP (VP (var "n")), LConsP WildP (VP (var "xs"))] (App (App (App (Global "index") (V (var "t"))) (V (var "n"))) (V (var "xs")))
    ]

explicitIndexDepDecl :: Decl
explicitIndexDepDecl =
  Decl
    "indexDep"
    (PiT (var "t") TyT (PiT (var "n") NatT (PiT (var "i") (FinT (V (var "n"))) (PiT (var "l") (VectT (V (var "t")) (V (var "n"))) (V (var "t"))))))
    [ Clause [WildP, WildP, FZP, VConsP (VP (var "x")) WildP] (V (var "x")),
      Clause [VP (var "t"), SP (VP (var "j")), FSP (VP (var "f")), VConsP WildP (VP (var "xs"))] (App (App (App (App (Global "indexDep") (V (var "t"))) (V (var "j"))) (V (var "f"))) (V (var "xs")))
    ]

explicitDropDecl :: Decl
explicitDropDecl =
  Decl
    "drop"
    (PiT (var "t") TyT (PiT (var "i") NatT (PiT (var "l") (ListT (V (var "t"))) (ListT (V (var "t"))))))
    [ Clause [WildP, ZP, VP (var "xs")] (V (var "xs")),
      Clause [WildP, SP (VP (var "i")), LNilP] LNil,
      Clause [VP (var "t"), SP (VP (var "i")), LConsP WildP (VP (var "xs"))] (App (App (App (Global "drop") (V (var "t"))) (V (var "i"))) (V (var "xs")))
    ]

sym :: Decl
sym =
  Decl
    "sym"
    ( PiT
        (var "t")
        TyT
        ( PiT
            (var "x")
            ( V (var "t")
            )
            ( PiT
                (var "y")
                (V (var "t"))
                (PiT (var "p") (EqT (V (var "x")) (V (var "y"))) (EqT (V (var "y")) (V (var "x"))))
            )
        )
    )
    [ Clause [WildP, WildP, WildP, ReflP (VP (var "z"))] (Refl (V (var "z")))
    ]

trans :: Decl
trans =
  Decl
    "trans"
    ( PiT
        (var "t")
        TyT
        ( PiT
            (var "x")
            ( V (var "t")
            )
            ( PiT
                (var "y")
                (V (var "t"))
                ( PiT
                    (var "z")
                    (V (var "t"))
                    ( PiT
                        (var "p")
                        (EqT (V (var "x")) (V (var "y")))
                        ( PiT
                            (var "q")
                            (EqT (V (var "y")) (V (var "z")))
                            ( EqT (V (var "x")) (V (var "z"))
                            )
                        )
                    )
                )
            )
        )
    )
    [Clause [WildP, WildP, WildP, WildP, ReflP (VP (var "w")), ReflP (VP (var "v"))] (Refl (V (var "v")))]

main :: IO ()
main = checkProg $ Program [explicitIndexDecl, explicitDropDecl, explicitIndexDepDecl, sym, trans]

-- Some inference to try out:
-- main = infer (App (App (Lam (var "q") (Lam (var "v") (Pair (V (var "v")) (V (var "q"))))) (S Z)) Z)
-- main = infer (LCons (MJust Z) (LCons (MNothing) (LNil)))
-- main = infer (Lam (var "q") (V (var "q")))
-- main = check (FS FZ) (FinT (S (S (S Z))))
-- main = infer (Refl Z)
