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
  putStrLn $ "Checking program: " ++ show p
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

main :: IO ()
-- main = checkProg $ Program [explicitIndexDecl]

-- main = infer (App (App (Lam (var "q") (Lam (var "v") (Pair (V (var "v")) (V (var "q"))))) (S Z)) Z)
-- main = infer (LCons (MJust Z) (LCons (MNothing) (LNil)))

-- main = infer (Lam (var "q") (V (var "q")))

-- main = check (FS FZ) (FinT (S (S (S Z))))
main = infer (Refl Z)
