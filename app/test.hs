module Examples.Test (showAll) where

import Checking.Typechecking (checkTerm)
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
import Refactoring.RenameVars (renameVars_clause) 




testFileName :: String
testFileName = "../app/Examples/test.fluid"

getAST :: String -> String -> Program 
getAST fname fContents = case parseProgram fname fContents of 
                            Left errStr -> Program [] --failed
                            Right prog -> prog


--------------------------



--------------------------

--given data name, and constructor name, positions I of the index to unify (index from 0, right to left), 
--all variables in I\I1 will now have the name of I1
--TODO: move the biggest number in I to the front so that we retain the earliest var
tryRefactor:: String ->  String -> String -> Program 
tryRefactor codeStr oldVarName newVarName =  
    let ast = getAST testFileName codeStr in 
        case ast of 
            Program items -> case  items !! 3 of 
                                Decl decl ->  Program [(Decl (DeclItem  "test" NatT [(renameVars_clause ("n") ("m")  ((declClauses decl)!!0) )]))]
                                Data decl ->  Program [Data decl]




showAll :: IO ()
showAll = do
  putStrLn ""
 -- print testData
  putStrLn "original code:"
  fluidCode <- readFile testFileName
  putStrLn fluidCode
  putStrLn "refactored code:"
  print (tryRefactor fluidCode "Data2" "C21")  
  putStrLn ""



