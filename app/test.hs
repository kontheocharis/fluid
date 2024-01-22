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
import Refactoring.UnifyConstrIndices (unifyIndices_ast)




testFileName :: String
testFileName = "../app/Examples/test.fluid"

getAST :: String -> String -> Program 
getAST fname fContents = case parseProgram fname fContents of 
                            Left errStr -> Program [] --failed
                            Right prog -> prog


--------------------------


--given data name, and constructor name, positions I of the index to unify (index from 0, right to left), 
--all variables in I\I1 will now have the name of I1
--TODO: move the biggest number in I to the front so that we retain the earliest var
tryRefactor:: String ->  String -> String -> [Int] -> Program 
tryRefactor codeStr datName constrName indPosns =  
    let ast = getAST testFileName codeStr in 
        unifyIndices_ast datName constrName indPosns ast 
            




showAll :: IO ()
showAll = do
  putStrLn ""
 -- print testData
  putStrLn "original code:"
  fluidCode <- readFile testFileName
  putStrLn fluidCode
  putStrLn "refactored code:"
 -- print (tryRefactor fluidCode "Data1" "C1" [5,4])  
  print (tryRefactor fluidCode "Data2" "C21" [3,2])  
  putStrLn ""


{-
original code:
data Data1 : List Nat -> Type  where
    | C1 : (ind1 : List Nat) -> (ind2 : List Nat) -> (a:Type) -> (n: Nat) -> Data1 ind1 -> Data1 ind2
    | C2 : (ind : List Nat) -> Nat -> Data1 ind
    | C3 : (ind :List Nat) -> Data1 ind


data Data2 : Nat -> Type  where
    | C21 : (n1: Nat) -> (n2:Nat) -> (n3:Nat) -> Data2 n2


g: (n1:Nat) -> (n2:Nat) -> (n3:Nat) ->  Data2 n2
g n1 n2 n3  = C21 n1 n2 n3


h: (n:Nat) -> (Data2 n) -> Nat
h n2 (C21 n1 n2 n3) = n2


refactored code:
data Data1 : (n0 : [Nat]) -> Type where
  | C1 : (ind1 : [Nat]) -> (ind2 : [Nat]) -> (a : Type) -> (n : Nat) -> (n8 : (Data1 ind1)) -> (Data1 ind2)
  | C2 : (ind : [Nat]) -> (n11 : Nat) -> (Data1 ind)
  | C3 : (ind : [Nat]) -> (Data1 ind)

data Data2 : (n13 : Nat) -> Type where
  | C21 : (n1 : Nat) -> (n3 : Nat) -> (Data2 n1)

g : (n1 : Nat) -> (n2 : Nat) -> (n3 : Nat) -> (Data2 n2)
g n1 n2 n3 = ((C21 ?n1_2) n3)

h : (n : Nat) -> (n23 : (Data2 n)) -> Nat
h n2 ((C21 n1) n3) = n2

-}


    


