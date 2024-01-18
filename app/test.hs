module Examples.Test (showAll) where


import Parsing.Parser (parseProgram)
import Lang
  ( Program (..),
    Term (..),
   )
import Refactoring.SpecialiseConstructorIndex (specConstr_ast)

testFileName :: String
testFileName = "../app/Examples/test.fluid"

getAST :: String -> String -> Program 
getAST fname fContents = case parseProgram fname fContents of 
                            Left errStr -> Program [] --failed
                            Right prog -> prog


--------------------------


--given data name, and constructor name, position of the index to specialise, what it should specialise to
tryRefactor:: String ->  String -> String -> Int -> Term -> Program 
tryRefactor codeStr datName constrName indPosn resTerm =  
    let ast = getAST testFileName codeStr in 
        specConstr_ast datName constrName indPosn resTerm ast



showAll :: IO ()
showAll = do
  putStrLn ""
 -- print testData
  putStrLn ""
  fluidCode <- readFile testFileName
  putStrLn fluidCode
  putStrLn ""
  print (tryRefactor fluidCode "Data1" "C2" 0 LNil)
  putStrLn ""





    




