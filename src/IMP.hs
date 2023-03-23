module IMP (module IMP) where
import Data.Maybe (fromJust)
import GHC.Data.Maybe (rightToMaybe)

data AExp = Num Int 
           | VarA String 
           | Add AExp AExp 
           | Mul AExp AExp 
           | Sub AExp AExp 

data BExp = T | F 
           | Equal BExp BExp 
           | LTE BExp BExp 
           | Not BExp 
           | And BExp BExp 

data SExp = Assign String AExp 
           | Skip 
           | Seq SExp SExp 
           | If BExp SExp SExp 
           | While BExp SExp
           | Call String [String]

data DExp = DCons String [String] SExp DExp
          | DMain SExp

{-
  Procedures are only side-effecting: they can define local variables, but
  these cannot be used outside of that procedure. In order to get a value out
  you have to pass in a variable that will be updated.
-}

--------------------------------
-- Semantic functions ----------
--------------------------------
data Value = I Int | B Bool 
   deriving (Show)

type Proc = ([String], SExp)
type State = [(String, Either Proc Value)]

isProc :: Either Proc Value -> Bool
isProc (Left _) = True
isProc (Right _) = False

fromRight :: Either a b -> b
fromRight = fromJust . rightToMaybe

look :: State -> String -> Either Proc Value
look [] y = error $ "Cannot find " ++ y ++ " in state" 
look ((x,v) : xs) y 
  | x == y = v 
  | otherwise = look xs y 

subs :: State -> String -> Value -> State 
subs [] y v2 = [(y,Right v2)]
subs ((x,_) : xs) y v2 
   | x == y = (x,Right v2) : xs 
   | otherwise = subs xs y v2

evalA :: AExp -> State -> Int
evalA (Num n) s     = n 
evalA (VarA x) s    =
  case look s x of
    Right (I n') -> n'
    Right (B _ ) -> error "type error: found boolean, expecting integer"
    Left _ -> error "type error: found procedure, expecting integer"
evalA (Add a1 a2) s = (evalA a1 s) + (evalA a2 s)
evalA (Mul a1 a2) s = (evalA a1 s) * (evalA a2 s)
evalA (Sub a1 a2) s = (evalA a1 s) - (evalA a2 s)

evalB :: BExp -> State -> Bool
evalB T s = True 
evalB F s = False 
evalB (Equal a1 a2) s = (evalB a1 s) == (evalB a2 s)
evalB (LTE a1 a2) s = (evalB a1 s) <= (evalB a2 s)
evalB (Not a1) s = not (evalB a1 s) 
evalB (And a1 a2) s = (evalB a1 s) && (evalB a2 s)

---------------------------------------------
--- big-step, natural, operational semantics
---------------------------------------------

evalBS :: SExp -> State -> State  
evalBS (Assign x a) s = subs s x $ I (evalA a s)
evalBS Skip s = s 
evalBS (Seq s1 s2) s =
    let s'  = evalBS s1 s 
        s'' = evalBS s2 s' 
    in s''  
evalBS (If b s1 s2) s 
  | evalB b s        = evalBS s1 s 
  | otherwise        = evalBS s2 s 
evalBS (While b ss) s 
   | evalB b s       = 
             let s'  = evalBS ss s 
                 s'' = evalBS (While b ss) s' 
             in s''
   | otherwise       = s 
evalBS (Call f xs) s = undefined

evalBP :: DExp -> State -> State
evalBP (DCons f xs b k) s = evalBP k ((f,Left (xs, b)) : s)
evalBP (DMain k) s = evalBS k s

