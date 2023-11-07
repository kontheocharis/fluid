module Main (main) where

import Clauses (expandDeclFully)
import Control.Monad.State (StateT (runStateT), runState)
import Examples.Drop (dropDecl)
import Examples.Index (indexDecl)
import Lang (Clause (..), Decl (Decl), Pat (..), Program (..), Term (..))
import Ornamenting (ornamentDecl)
import Typechecking (TcState (..), emptyTcState, inferTerm, normaliseTermFully, unifyTerms, unifyToLeft)
import Vars (var)

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

infer :: Term -> IO ()
infer a = do
  putStrLn $ "Inferring " ++ show a
  case runStateT (inferTerm a) emptyTcState of
    Left err -> putStrLn $ "Error: " ++ show err
    Right (s, _) -> putStrLn $ "Result: " ++ show a ++ " : " ++ show s

main :: IO ()
main = infer (App (App (Lam (var "q") (Lam (var "v") (Pair (V (var "v")) (V (var "q"))))) (S Z)) Z)

-- main = infer (Lam (var "q") (Pair (V (var "q")) Z))
