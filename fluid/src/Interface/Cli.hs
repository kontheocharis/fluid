module Interface.Cli (runCli) where

import Checking.Context (Tc, runTc)
import Checking.Typechecking (checkProgram, inferTerm, normaliseTermFully, runUntilFixpoint, substituteHolesIn)
import Checking.Vars (subInM)
import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.Functor ((<&>))
import Data.String
import Data.Text.IO (hPutStrLn)
import Lang (TermMappable)
import Options.Applicative (execParser, (<**>), (<|>))
import Options.Applicative.Builder (fullDesc, header, help, info, long, progDesc, short, strOption, switch)
import Options.Applicative.Common (Parser)
import Options.Applicative.Extra (helper)
import Parsing.Parser (parseProgram, parseTerm)
import System.Console.Haskeline (InputT, defaultSettings, getInputLine, outputStrLn, runInputT)
import System.Exit (exitFailure)
import System.IO (stderr)

-- | What mode to run in.
data Mode
  = -- | Typecheck a file.
    CheckFile String
  | -- | Run a REPL
    Repl
  deriving (Show)

newtype Flags = Flags
  { -- | Whether to dump the parsed program.
    dumpParsed :: Bool
  }
  deriving (Show)

data Args = Args
  { argsMode :: Mode,
    argsFlags :: Flags
  }
  deriving (Show)

-- | Parse the command-line flags.
parseFlags :: Parser Flags
parseFlags = Flags <$> switch (long "dump-parsed" <> help "Print the parsed program")

-- | Parse the mode to run in.
parseMode :: Parser Mode
parseMode = (CheckFile <$> strOption (long "check" <> short 'c' <> help "File to check")) <|> pure Repl

-- | Parse the command line arguments.
parseArgs :: Parser Args
parseArgs = Args <$> parseMode <*> parseFlags

-- | Run the main CLI.
runCli :: IO ()
runCli = do
  args <- execParser opts
  runCompiler args
  where
    opts =
      info
        (parseArgs <**> helper)
        ( fullDesc
            <> progDesc "Fluid is a toy dependently typed programming language for experimenting with automated program transformations. A REPL is available if no arguments are given."
            <> header "Fluid"
        )

-- | Log a message.
msg :: String -> InputT IO ()
msg m = do
  outputStrLn m
  return ()

-- | Log a message to stderr and exit with an error code.
err :: String -> InputT IO a
err m = liftIO $ do
  hPutStrLn stderr $ fromString m
  exitFailure

-- | Log a message.
replErr :: String -> InputT IO a
replErr m = do
  msg m
  runRepl

-- | Run the compiler.
runCompiler :: Args -> IO ()
runCompiler (Args (CheckFile file) flags) = runInputT defaultSettings $ do
  msg $ "Parsing file " ++ file
  contents <- liftIO $ readFile file
  parsed <- handleParse err (parseProgram file contents)
  when (dumpParsed flags) $ msg $ "Parsed program:\n" ++ show parsed
  checked <- handleTc err (checkProgram parsed)
  msg "\nTypechecked program successfully"
  when (dumpParsed flags) $ msg $ "Parsed + checked program:\n" ++ show checked
runCompiler (Args Repl _) = runInputT defaultSettings runRepl

-- | Run the REPL.
runRepl :: InputT IO a
runRepl = do
  i <- getInputLine "> "
  case i of
    Nothing -> return ()
    Just ('@' : 't' : ' ' : inp) -> do
      t <- handleParse replErr (parseTerm inp)
      ty <- handleTc replErr (inferTerm t)
      outputStrLn $ show ty
    Just inp | all isSpace inp -> return ()
    Just inp -> do
      t <- handleParse replErr (parseTerm inp)
      _ <- handleTc replErr (inferTerm t)
      t' <- handleTc replErr (normaliseTermFully t)
      outputStrLn $ show t'
  runRepl

-- | Handle a parsing result.
handleParse :: (String -> InputT IO a) -> Either String a -> InputT IO a
handleParse er res = do
  case res of
    Left e -> er $ "Failed to parse: " ++ e
    Right p -> return p

-- | Handle a checking result.
handleTc :: (Eq a, TermMappable a) => (String -> InputT IO a) -> Tc a -> InputT IO a
handleTc er a = do
  case runTc (runUntilFixpoint a) of
    Left e -> er $ "Error: " ++ show e
    Right p -> return p
