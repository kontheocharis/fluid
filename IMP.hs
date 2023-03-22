module IMP where

data Aexp = Num Int 
           | VarA String 
           | Add Aexp Aexp 
           | Mul Aexp Aexp 
           | Sub Aexp Aexp 

data Bexp = T | F 
           | Equal Bexp Bexp 
           | LTE Bexp Bexp 
           | Not Bexp 
           | And Bexp Bexp 

data Sexp = Assign String Aexp 
           | Skip 
           | Seq Sexp Sexp 
           | If Bexp Sexp Sexp 
           | While Bexp Sexp

--------------------------------
-- Semantic functions ----------
--------------------------------
data Value = I Int | B Bool 
   deriving (Show)

type State = [(String, Value)]

look :: State -> String -> Value
look [] y = error $ "Cannot find " ++ y ++ " in state" 
look ((x,v) : xs) y 
  | x == y = v 
  | otherwise = look xs y 

subs :: State -> String -> Value -> State 
subs [] y v2 = [(y,v2)]
subs ((x,v) : xs) y v2 
   | x == y = (x,v2) : xs 
   | otherwise = subs xs y v2

evalA :: Aexp -> State -> Int
evalA (Num n) s     = n 
evalA (VarA x) s    = case look s x of
                         I n' -> n' 
evalA (Add a1 a2) s = (evalA a1 s) + (evalA a2 s)
evalA (Mul a1 a2) s = (evalA a1 s) * (evalA a2 s)
evalA (Sub a1 a2) s = (evalA a1 s) - (evalA a2 s)

evalB :: Bexp -> State -> Bool
evalB T s = True 
evalB F s = False 
evalB (Equal a1 a2) s = (evalB a1 s) == (evalB a2 s)
evalB (LTE a1 a2) s = (evalB a1 s) <= (evalB a2 s)
evalB (Not a1) s = not (evalB a1 s) 
evalB (And a1 a2) s = (evalB a1 s) && (evalB a2 s)

---------------------------------------------
--- big-step, natural, operational semantics
---------------------------------------------

evalBS :: Sexp -> State -> State  
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