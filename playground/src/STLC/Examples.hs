module Examples where

import Typecheck
import Eval
import Syntax
import Parser

id' = Lam (Inf (Bound 0))

const' = Lam (Lam (Inf (Bound 1)))



free x = Inf (Free (Global x))

term1 = Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y"

term1T = 
  do
     Just x <- parse "" (parseTermInf 0 [""]) "((\\x -> x) :: a -> a) y"
     putStrLn $ show $ typeInf0 env1 x

term1E = 
  do
     Just x <- parse "" (parseTermInf 0 [""]) "((\\x -> x) :: a -> a) y"
     putStrLn $ show $ quote0 (evalInf x [])

term2 = Ann const' (Fun (Fun (tfree "b") (tfree "b"))
                        (Fun (tfree "a")
                             (Fun (tfree "b") (tfree "b"))))
         :@: id' :@: free "y"

term2T =
  do
     Just x <- parse "" (parseTermInf 0 [""]) "((\\x y -> x) :: (b -> b) -> a -> b -> b) (\\x -> x) y"
     putStrLn $ show $ typeInf0 env2 x

term2E = do
     Just x <- parse "" (parseTermInf 0 [""]) "((\\x y -> x) :: (b -> b) -> a -> b -> b) (\\x -> x) y"
     putStrLn $ show $ quote0 (evalInf x [])

env1 = [(Global "y", HasType (tfree "a")), (Global "a", HasKind Star)]

env2 = [(Global "b", HasKind Star)] ++ env1

