module Examples.Test (showAll) where

import Parsing.Parser (parseProgram)
import Lang
  ( Clause (..),
    CtorItem (..),
    DataItem (..),
    DeclItem (..),
    GlobalName,
    Item (..),
    Pat,
    Program (..),
    Term (..),
    Type,
    Var (..),
    piTypeToList,
    listToPiType
  )
import Refactoring.RemoveMaybe (removeMaybe_ast) 


testFileName :: String
testFileName = "../app/Examples/test.fluid"

getAST :: String -> String -> Program 
getAST fname fContents = case parseProgram fname fContents of 
                            Left errStr -> Program [] --failed
                            Right prog -> prog


--------------------------

--------------------------

--given function name with Maybe T as resulting type, 
--check that there are no Nothing cases
--if so, remove Maybe
--for now, assume that there are no other Maybes (TODO)
tryRefactor:: String -> String -> Program 
tryRefactor codeStr  funcName =  
    let ast = getAST testFileName codeStr in 
        removeMaybe_ast funcName ast       




showAll :: IO ()
showAll = do
  putStrLn ""
  putStrLn "original code:"
  fluidCode <- readFile testFileName
  putStrLn fluidCode
  putStrLn "refactored code:"
  print (tryRefactor fluidCode "f")  
  putStrLn ""



{-
original code:
f: (n:Nat) -> Maybe Nat
f Z = Just Z
f (S n) = Just Z


refactored code:
f : (n : Nat) -> Nat
f Z = Z
f (S n) = Z

-}