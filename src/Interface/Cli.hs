{-# LANGUAGE LambdaCase #-}

module Interface.Cli (runCli) where

import Checking.Context (Tc, TcState, emptyTcState, runTcAndGetState)
import Checking.Typechecking (checkProgram, inferTerm, normaliseTermFully)
import Control.Monad (when)
import Control.Monad.Cont (MonadIO (liftIO))
import Control.Monad.State (MonadState (put))
import Data.Char (isSpace)
import Data.String
import Data.Text.IO (hPutStrLn)
import Lang (Program (..))
import Options.Applicative (execParser, value, (<**>), (<|>))
import Options.Applicative.Builder (fullDesc, header, help, info, long, maybeReader, option, progDesc, short, strOption, switch)
import Options.Applicative.Common (Parser)
import Options.Applicative.Extra (helper)
import Parsing.Parser (parseProgram, parseTerm)
import Resources.Prelude (preludeContents, preludePath)
import System.Console.Haskeline (InputT, defaultSettings, getInputLine, outputStrLn, runInputT)
import System.Exit (exitFailure)
import System.IO (stderr)
import Text.Read (readMaybe)

-- | The kind of an argument that might be given to a refactoring.
data RefactorArgKind = Name String | Idx Int | Loc Int Int deriving (Show)

-- | Opaque arguments given to a refactoring as key-value pairs.
--
-- These depend on the refactoring being applied.
newtype RefactorArgs = RefactorArgs [(String, RefactorArgKind)] deriving (Show)

-- | What mode to run in.
data Mode
  = -- | Typecheck a file.
    CheckFile String
  | -- | Run a REPL
    Repl
  | -- | Apply a refactoring to a file.
    Refactor String
  deriving (Show)

-- | How to apply changes to a file
data ApplyChanges = InPlace | Print | NewFile
  deriving (Show)

data Flags = Flags
  { -- | Whether to dump the parsed program.
    dumpParsed :: Bool,
    -- | How to apply a refactoring.
    applyChanges :: ApplyChanges,
    -- | Refactoring to apply.
    refactorName :: Maybe String,
    -- | Refactoring-specific arguments.
    refactorArgs :: RefactorArgs
  }
  deriving (Show)

data Args = Args
  { argsMode :: Mode,
    argsFlags :: Flags
  }
  deriving (Show)

-- | Parse the command-line flags.
parseFlags :: Parser Flags
parseFlags =
  Flags
    <$> switch (long "dump-parsed" <> help "Print the parsed program")
    <*> option
      ( maybeReader $ \case
          "in-place" -> Just InPlace
          "print" -> Just Print
          "new-file" -> Just NewFile
          _ -> Nothing
      )
      ( long "apply-changes"
          <> help "Select how to apply changes induced by a refactoring ('print' [default] / 'in-place' / 'new-file')"
          <> value Print
      )
    <*> option (maybeReader (Just . Just)) (short 'n' <> long "refactor-name" <> help "Name of the refactoring to apply" <> value Nothing)
    <*> option
      ( maybeReader $ \s -> do
          parsedArgs <- mapM readRefactorArg (words s)
          return $ RefactorArgs parsedArgs
      )
      ( long "refactor-args"
          <> short 'a'
          <> help
            ( "If -r and -n are chosen, provide arguments relevant to the chosen refactoring."
                ++ " Arguments are of the form <name>=<argument> where <argument> is either an index <n>, name <x> or location <l>:<c>"
            )
          <> value (RefactorArgs [])
      )

-- | Parse a refactoring argument.
readRefactorArg :: String -> Maybe (String, RefactorArgKind)
readRefactorArg v = do
  (l, c) <- split '=' v
  k <- readRefactorArgKind c
  return (l, k)

-- | Parse a refactoring argument kind.
readRefactorArgKind :: String -> Maybe RefactorArgKind
readRefactorArgKind v = case split ':' v of
  Just (l, c) -> Loc <$> readMaybe l <*> readMaybe c
  Nothing -> case readMaybe v of
    Just i -> Just $ Idx i
    Nothing -> Just $ Name v

-- | Split a string on a character at the first occurrence (not including the character itself).
split :: Char -> String -> Maybe (String, String)
split ch s = case break (== ch) s of
  (k, x : v) | x == ch -> Just (k, v)
  _ -> Nothing

-- | Parse the mode to run in.
parseMode :: Parser Mode
parseMode =
  (CheckFile <$> strOption (long "check" <> short 'c' <> help "File to check"))
    <|> (Refactor <$> strOption (long "refactor" <> short 'r' <> help "File to refactor. Provide the name of the refactoring with -n and any relevant arguments using -a."))
    <|> pure Repl

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
  (preludeProgram, tcState) <- parseAndCheckPrelude
  parsed <- handleParse err (parseProgram file contents (Just preludeProgram))
  when (dumpParsed flags) $ msg $ "Parsed program:\n" ++ show parsed
  checked <- handleTc err (put tcState >> checkProgram parsed)
  msg "\nTypechecked program successfully"
  when (dumpParsed flags) $ msg $ "Parsed + checked program:\n" ++ show checked
runCompiler (Args Repl _) = runInputT defaultSettings runRepl
runCompiler (Args (Refactor f) Flags {refactorArgs = a, refactorName = n}) = putStrLn $ "Got file " ++ show f ++ " and args " ++ show a ++ " and name " ++ show n

-- | Run the REPL.
runRepl :: InputT IO a
runRepl = do
  i <- getInputLine "> "
  (_, tcState) <- parseAndCheckPrelude -- @@Todo: be in TC monad so that state is retained.
  case i of
    Nothing -> return ()
    Just ('@' : 't' : ' ' : inp) -> do
      t <- handleParse replErr (parseTerm inp)
      ty <- handleTc replErr (put tcState >> inferTerm t)
      outputStrLn $ show ty
    Just inp | all isSpace inp -> return ()
    Just inp -> do
      t <- handleParse replErr (parseTerm inp)
      _ <- handleTc replErr (put tcState >> inferTerm t)
      t' <- handleTc replErr (put tcState >> normaliseTermFully t)
      outputStrLn $ show t'
  runRepl

-- | Handle a parsing result.
handleParse :: (String -> InputT IO a) -> Either String a -> InputT IO a
handleParse er res = do
  case res of
    Left e -> er $ "Failed to parse: " ++ e
    Right p -> return p

-- | Handle a checking result.
handleTc :: (String -> InputT IO a) -> Tc a -> InputT IO a
handleTc er a = fst <$> handleTcAndGetState er a

-- | Handle a checking result and return the state.
handleTcAndGetState :: (String -> InputT IO a) -> Tc a -> InputT IO (a, TcState)
handleTcAndGetState er a = do
  case runTcAndGetState a of
    Left e -> do
      x <- er $ "Error: " ++ show e
      return (x, emptyTcState)
    Right p -> return p

-- | Parse and check the Prelude, returning the final TC state and the parsed program.
parseAndCheckPrelude :: InputT IO (Program, TcState)
parseAndCheckPrelude = do
  parsed <- handleParse err (parseProgram preludePath preludeContents Nothing)
  msg "Parsed prelude: " >> msg (show parsed)
  (checked, state) <- handleTcAndGetState err (checkProgram parsed)
  return (checked, state)
