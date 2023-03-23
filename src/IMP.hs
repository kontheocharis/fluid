module IMP (module IMP) where

import Data.Maybe (fromJust)
import GHC.Data.Maybe (rightToMaybe)
import Data.Bifunctor (second)
import Data.Biapplicative (biliftA2)
import Data.Either (isLeft)
import Data.Text.Lazy (unpack)
import Text.Pretty.Simple (pShowLightBg)

-------------------------------------------------------------------------------
-- [Pretty Printing] ----------------------------------------------------------
-------------------------------------------------------------------------------

ppShow :: Show a => a -> String
ppShow = unpack . pShowLightBg

ppPrint :: Show a => a -> IO ()
ppPrint = putStrLn . unpack . pShowLightBg

-------------------------------------------------------------------------------
-- [Syntax] -------------------------------------------------------------------
-------------------------------------------------------------------------------

data AExp = Num Int 
          | VarA String 
          | Add AExp AExp 
          | Mul AExp AExp 
          | Sub AExp AExp 
          deriving (Show)

data BExp = T | F 
          | Equal BExp BExp 
          | LTE AExp AExp 
          | Not BExp 
          | And BExp BExp 
          deriving (Show)

data SExp = Assign String AExp 
          | Skip 
          | Seq SExp SExp 
          | If BExp SExp SExp 
          | While BExp SExp
          | Call String [String]
          deriving (Show)

data DExp = DCons String [String] SExp DExp
          | DMain SExp
          deriving (Show)

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
isProc = isLeft

argOrProc :: [String] -> (String, Either Proc Value) -> Bool
argOrProc args (x,v) = x `elem` args || isProc v

fromRight :: Either a b -> b
fromRight = fromJust . rightToMaybe

look :: State -> String -> Either Proc Value
look [] y = error $ "Cannot find " ++ y ++ " in state" 
look ((x,v) : xs) y 
  | x == y = v 
  | otherwise = look xs y 

subs :: State -> String -> Value -> State 
subs [] y v2 = [(y,Right v2)]
subs ((x,v1) : xs) y v2 
   | x == y = (x,Right v2) : xs 
   | otherwise = (x,v1) : subs xs y v2

fvA :: [String] -> AExp -> [String]
fvA _   (Num _) = []
fvA env (VarA x)
  | x `elem` env = []
  | otherwise = [x]
fvA env (Add x y) = fvA env x ++ fvA env y
fvA env (Mul x y) = fvA env x ++ fvA env y
fvA env (Sub x y) = fvA env x ++ fvA env y

fv :: [String] -> SExp -> [String]
fv env0 = snd . fv' env0 where
  fv' :: [String] -> SExp -> ([String], [String])
  fv' env (Assign x v) = (x : env, fvA (x : env) v)
  fv' env Skip = (env, [])
  fv' env (Seq s k) = let (env', xs) = fv' env s in second (xs ++) (fv' env' k)
  fv' env (If _ tt ff) = biliftA2 (++) (++) (fv' env tt) (fv' env ff)
  fv' env (While _ k) = fv' env k
  fv' env (Call f xs) = (f : env, filter (`notElem` env) xs)

replace :: String -> String -> [String] -> [String]
replace x y = map (\z -> if x == z then y else z) 

type EitherOr a = Either a a
fromEitherOr :: EitherOr a -> a
fromEitherOr (Left x) = x
fromEitherOr (Right x) = x

fmap :: (a -> b) -> EitherOr a -> EitherOr b
fmap f (Left x) = Left (f x)
fmap f (Right x) = Right (f x)

subsA :: String -> String -> AExp -> AExp
subsA _ _ a@(Num _) = a
subsA src dst a@(VarA x)
  | src == x = VarA dst
  | otherwise = a
subsA src dst (Add x y) = Add (subsA src dst x) (subsA src dst y)
subsA src dst (Mul x y) = Mul (subsA src dst x) (subsA src dst y)
subsA src dst (Sub x y) = Sub (subsA src dst x) (subsA src dst y)

subsB :: String -> String -> BExp -> BExp
subsB src dst (LTE x y) = LTE (subsA src dst x) (subsA src dst y)
subsB _ _ b = b

subsS :: String -> String -> SExp -> SExp
subsS src dst = fromEitherOr . subsS' where
  subsS' :: SExp -> EitherOr SExp
  subsS' s0@(Assign x e)
    | src == x = Left s0
    | otherwise = Right (Assign x (subsA src dst e))
  subsS' Skip = Right Skip
  subsS' (Seq s k) =
    case subsS' s of
      Left s' -> Left (Seq s' k)
      Right s' -> IMP.fmap (Seq s') (subsS' k)
  subsS' (If e tt ff) =
    case (subsS' tt, subsS' ff) of
      (Left tt', ff') -> Left (If (subsB src dst e) tt' (fromEitherOr ff'))
      (tt', Left ff') -> Left (If (subsB src dst e) (fromEitherOr tt') ff')
      (tt',ff') ->
        Right (If (subsB src dst e) (fromEitherOr tt') (fromEitherOr ff'))
  subsS' (While e k) = IMP.fmap (While (subsB src dst e)) (subsS' k)
  subsS' (Call f xs) = Right (Call f (replace src dst xs))

type Find = [String]
type Replace = [String]
subsAllS :: Find -> Replace -> SExp -> SExp
subsAllS src dst stmt
  | any (`elem` fv src stmt) dst = error "variable capture"
  | otherwise = foldr (uncurry subsS) stmt (zip src dst)

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
evalB (LTE a1 a2) s = evalA a1 s <= evalA a2 s
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
evalBS (Call f xs) s =
  case look s f of
    Right _ -> error "type error: found value, expecting procedure"
    Left (args,body) ->
      let body' = subsAllS args xs body
          s' = evalBS body' (filter (argOrProc xs) s)
          -- s'' = filter (argOrProc xs) s'
          -- FIXME: we do not properly revert the state following a proc call
      in s'

evalBP :: DExp -> State -> State
evalBP (DCons f xs b k) s = evalBP k ((f,Left (xs, b)) : s)
evalBP (DMain k) s = evalBS k s

ppEvalBP :: DExp -> IO ()
ppEvalBP p = ppPrint (evalBP p [])

