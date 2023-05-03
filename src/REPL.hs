module REPL where

import Prelude hiding (print, (<>))
import Control.Monad.Except
import Data.List
import Data.Char
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language
import System.IO hiding (print)
import System.IO.Error


-- import Common
import Syntax
import Typecheck
import Parser
import Eval

data Command = TypeOf String
             | Compile CompileForm
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- type Ctx inf = [(Name, inf)]
type State = (String, Env, Context)

data Interpreter i c t tinf =
  I { iname :: String,
      iprompt :: String,
      iitype :: [(Name, Value)] -> Context -> i -> Result t,
      iquote :: Value -> c,
      ieval  :: Env -> i -> Value,
      ihastype :: t -> Value,
      icprint :: c -> Doc,
      itprint :: t -> Doc,
      iiparse :: CharParser () i,
      isparse :: CharParser () (Stmt i tinf),
      iassume :: State -> (String, tinf) -> IO State }

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "List of commands:  Any command may be abbreviated to :c where\n" ++
     "c is the first character in the full name.\n\n" ++
     "<expr>                  evaluate expression\n" ++
     "let <var> = <expr>      define variable\n" ++
     "assume <var> :: <expr>  assume variable\n\n"
     ++
     unlines (map (\ (Cmd cs a _ d) -> let  ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) cs))
                                       in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":type"]        "<expr>"  TypeOf         "print type of expression",
       Cmd [":browse"]      ""        (const Browse) "browse names in scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "load program from file",
       Cmd [":quit"]        ""        (const Quit)   "exit interpreter",
       Cmd [":help",":?"]   ""        (const Help)   "display this list of commands" ]

dummy = makeTokenParser (haskellStyle { identStart = letter <|> P.char '_',
                                              reservedNames = [] })

parseIO :: String -> CharParser () a -> String -> IO (Maybe a)
parseIO f p x = case P.parse (whiteSpace dummy >> p >>= \ x -> eof >> return x) f x of
                  Left e  -> putStrLn (show e) >> return Nothing
                  Right r -> return (Just r)

readevalprint :: Interpreter i c t tinf -> State -> IO ()
readevalprint int state@(out, ve, te) =
  let rec int state =
        do
          putStr (iprompt int)
          hFlush stdout
          x <- catchIOError (fmap Just getLine) (\_ -> return Nothing)
          case x of
            Nothing   ->  return ()
            Just ""   ->
              rec int state
            Just x    ->
              do
                c  <- interpretCommand x
                state' <- handleCommand int state c
                maybe (return ()) (rec int) state'
  in
    do
      --  welcome
      putStrLn ("Interpreter for " ++ iname int ++ ".\n" ++
                             "Type :? for help.")
      --  enter loop
      rec int state

interpretCommand :: String -> IO Command
interpretCommand x
  =  if isPrefixOf ":" x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Unknown command `" ++ cmd ++ "'. Type :? for help.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             x   ->  do  putStrLn ("Ambiguous command, could be " ++ concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop
     else
       return (Compile (CompileInteractive x))

handleCommand :: Interpreter i c t tinf -> State -> Command -> IO (Maybe State)
handleCommand int state@(out, ve, te) cmd
  =  case cmd of
       Quit   ->  (putStrLn "!@#$^&*") >> return Nothing
       Noop   ->  return (Just state)
       Help   ->  putStr (helpTxt commands) >> return (Just state)
       TypeOf x ->
                  do  x <- parseIO "<interactive>" (iiparse int) x
                      t <- maybe (return Nothing) (iinfer int ve te) x
                      maybe (return ()) (\u -> putStrLn (render (itprint int u))) t
                      return (Just state)
       Browse ->  do  putStr (unlines [ s | Global s <- reverse (nub (map fst te)) ])
                      return (Just state)
       Compile c ->
                  do  state <- case c of
                                 CompileInteractive s -> compilePhrase int state s
                                 CompileFile f        -> compileFile int state f
                      return (Just state)

compileFile :: Interpreter i c t tinf -> State -> String -> IO State
compileFile int state@(out, ve, te) f =
  do
    x <- readFile f
    stmts <- parseIO f (many (isparse int)) x
    maybe (return state) (foldM (handleStmt int) state) stmts

compilePhrase :: Interpreter i c t tinf -> State -> String -> IO State
compilePhrase int state@(out, ve, te) x =
  do
    x <- parseIO "<interactive>" (isparse int) x
    maybe (return state) (handleStmt int state) x


iinfer int d g t =
  case iitype int d g t of
    Left e -> putStrLn e >> return Nothing
    Right v -> return (Just v)

handleStmt :: Interpreter i c t tinf
              -> State -> Stmt i tinf -> IO State
handleStmt int state@(out, ve, te) stmt =
  do
    case stmt of
        Assume ass -> foldM (iassume int) state ass
        Let x e    -> checkEval x e
        Eval e     -> checkEval it e
        PutStrLn x -> putStrLn x >> return state
        Out f      -> return (f, ve, te)
  where
    --  checkEval :: String -> i -> IO (State v inf)
    checkEval i t =
      check int state i t
        (\ (y, v) -> do
                       --  ugly, but we have limited space in the paper
                       --  usually, you'd want to have the bound identifier *and*
                       --  the result of evaluation
                       let outtext = if i == it then render (icprint int (iquote int v) <> text " :: " <> itprint int y)
                                                else render (text i <> text " :: " <> itprint int y)
                       putStrLn outtext
                       unless (null out) (writeFile out (process outtext)))
        (\ (y, v) -> ("", (Global i, v) : ve, (Global i, ihastype int y) : te))

check :: Interpreter i c t tinf -> State -> String -> i
         -> ((t, Value) -> IO ()) -> ((t, Value) -> State) -> IO State
check int state@(out, ve, te) i t kp k =
                do
                  -- i: String, t: Type
                  --  typecheck and evaluate
                  x <- iinfer int ve te t
                  case x of
                    Nothing  ->
                      do
                        --  putStrLn "type error"
                        return state
                    Just y   ->
                      do
                        let v = ieval int ve t
                        kp (y, v)
                        return (k (y, v))


it = "it"
process :: String -> String
process = unlines . map (\ x -> "< " ++ x) . lines