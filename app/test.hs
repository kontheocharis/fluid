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
import Refactoring.AddIndex (updataUsecaseInFunc_ast, updateUsecaseInCtor_ast, addIndex_ast) 




testFileName :: String
testFileName = "../app/Examples/test.fluid"

getAST :: String -> String -> Program 
getAST fname fContents = case parseProgram fname fContents of 
                            Left errStr -> Program [] --failed
                            Right prog -> prog


--------------------------

updateQueuedUsecase_ast :: String -> Type -> Int -> Program -> [(String)] -> (Program, [(String)]) 
updateQueuedUsecase_ast datName indexTy indPosn ast [] = (ast, [])
updateQueuedUsecase_ast datName indexTy indPosn ast (refact:queue) = 
    if ( refact)  == "useInFunc" then   
        let (refacted, newQ) = updataUsecaseInFunc_ast datName indexTy indPosn ast in --todo: use argument list
            updateQueuedUsecase_ast datName indexTy indPosn refacted (newQ ++ queue)
    else if ( refact)  == "useInCurrCtor" then   
        let refacted = updateUsecaseInCtor_ast datName indexTy indPosn ast in --todo: use argument list
            updateQueuedUsecase_ast datName indexTy indPosn refacted queue
    else --TODO: implement other refactoring   --other triggered refactoring should take in String that represents the arguments
        updateQueuedUsecase_ast datName indexTy indPosn ast queue
--e.g. if f is a function that uses Data1, then we would have added params to f, then any call of f elsewhere would need to be updated (not implemented)


--------------------------

--given data name, and index type to add, position of new index
--adds index before the current i position (right to left, from 0)
tryRefactor:: String ->  String -> Type -> Int -> Program
tryRefactor codeStr datName indexTy indPosn =  
    let ast = getAST testFileName codeStr in 
        if indPosn <0 then  
            ast
        else 
            let updatedData = addIndex_ast datName indexTy indPosn ast in         
                fst (updateQueuedUsecase_ast datName indexTy indPosn updatedData 
                                             [("useInFunc"), ("useInCurrCtor")])  --todo use arg list
                --["useAsIndex","useInOtherCtor"])


--todo: store args in a data structure instead of carrying all args
--TODO: possibly need a refactoring to reorder params




showAll :: IO ()
showAll = do
  putStrLn ""
 -- print testData
  putStrLn "original code:"
  fluidCode <- readFile testFileName
  putStrLn fluidCode
  putStrLn "refactored code:"
  print  (tryRefactor fluidCode "Data1" (ListT NatT) 1)  
  putStrLn ""




