module Examples where

import Typecheck
import Eval
import Syntax
import Parser

id' = Lam (Inf (Bound 0))

const' = Lam (Lam (Inf (Bound 1)))



free x = Inf (Free (Global x))

-- term1 = Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y"

printType t = case t of 
                    Left s -> putStrLn s
                    Right t' -> putStrLn $ Parser.print $ quote0 t'

term1T = 
  do
     Just x <- parse "" (parseITerm_ 0 [""]) "((\\x -> x) :: a -> a) y"
     printType $ typeInf0 env1 x
   

term1E = 
  do
     Just x <- parse "" (parseITerm_ 0 [""]) "((\\x -> x) :: a -> a) y"
     putStrLn $ show $ quote0 (evalInf x [])

--term2 = Ann const' (Fun (Fun (tfree "b") (tfree "b"))
--                        (Fun (tfree "a")
--                             (Fun (tfree "b") (tfree "b"))))
--         :@: id' :@: free "y"

term2T =
  do
     Just x <- parse "" (parseITerm_ 0 [""]) "((\\x y -> x) :: (b -> b) -> a -> b -> b) (\\x -> x) y"
     printType $ typeInf0 env2 x

term2E = do
     Just x <- parse "" (parseITerm_ 0 [""]) "((\\x y -> x) :: (b -> b) -> a -> b -> b) (\\x -> x) y"
     putStrLn $ show $ quote0 (evalInf x [])

term3T = 
  do
    Just x <- parse "" (parseITerm_ 0 [""]) "(\\a x -> x) :: forall(a :: *). a -> a"
    printType $ typeInf0 [] x

term4T = 
  do
     Just x <- parse "" (parseITerm_ 0 [""]) "((\\a x -> x) :: forall(a :: *). a -> a) Bool"
     printType $ typeInf0 env3 x

term5T = 
  do 
     Just x <- parse "" (parseITerm_ 0 [""]) "(((\\a x -> x) :: forall(a :: *). a -> a) Bool) False"
     printType $ typeInf0 env3 x

id2 = "(\\a x -> x) :: forall(a :: *). a -> a"

env1 = [(Global "y", vfree (Global "a")), (Global "a", VStar)]

env2 = [(Global "b", VStar)] ++ env1

env3 = [(Global "Bool", VStar), (Global "False", vfree (Global "Bool"))]

