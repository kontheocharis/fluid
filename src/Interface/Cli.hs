{-# LANGUAGE LambdaCase #-}

module Interface.Cli (runCli) where

import Checking.Context (Tc, TcState, runTc)
import Checking.Typechecking (checkProgram, inferTerm, normaliseTermFully)
import Control.Monad (void, when)
import Control.Monad.Cont (MonadIO (liftIO))
import Data.Char (isSpace)
import Data.String
import Data.Text.IO (hPutStrLn)
import Lang (Program)
import Options.Applicative (execParser, value, (<**>), (<|>))
import Options.Applicative.Builder (fullDesc, header, help, info, long, maybeReader, option, progDesc, short, strOption, switch)
import Options.Applicative.Common (Parser)
import Options.Applicative.Extra (helper)
import Parsing.Parser (parseProgram, parseRefactorArgs, parseTerm)
import Refactoring.SpecCtor (specCtor)
import Refactoring.RelCtorParams (relCtorParams)
import Refactoring.RelFuncParams (relFuncParams)
import Refactoring.RemoveMaybe (removeMaybe)
import Refactoring.Utils (FromRefactorArgs (..), Refact, RefactorArgs (..), evalRefact)
import System.Console.Haskeline (InputT, defaultSettings, getInputLine, outputStrLn, runInputT)
import System.Exit (exitFailure)
import System.IO (stderr)

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

-- | Command-line flags.
data Flags = Flags
  { -- | Whether to dump the parsed program.
    dumpParsed :: Bool,
    -- | Whether to be verbose.
    verbose :: Bool,
    -- | How to apply a refactoring.
    applyChanges :: ApplyChanges,
    -- | Refactoring to apply.
    refactorName :: Maybe String,
    -- | Refactoring-specific arguments.
    refactorArgs :: RefactorArgs
  }
  deriving (Show)

-- | Command-line arguments.
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
    <*> switch (long "verbose" <> short 'v' <> help "Be verbose")
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
          case parseRefactorArgs s of
            Left _ -> Nothing
            Right t -> Just t
      )
      ( long "refactor-args"
          <> short 'a'
          <> help
            ( "If -r and -n are chosen, provide arguments relevant to the chosen refactoring."
                ++ " Arguments are of the form <name>=<argument> where <argument> is either an index <n>, name <x>, index list [<n1>,..,<ni>], or location <l>:<c>"
            )
          <> value (RefactorArgs [])
      )

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
  runInputT defaultSettings $ runCompiler args
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
runCompiler :: Args -> InputT IO ()
runCompiler (Args (CheckFile file) flags) = void (parseAndCheckFile file flags)
runCompiler (Args Repl _) = runRepl
runCompiler (Args (Refactor f) fl@(Flags {refactorArgs = a, refactorName = Just n})) = case n of
  "spec-ctor" -> applyRefactoring f a fl specCtor
  "rel-ctor-params" -> applyRefactoring f a fl relCtorParams
  "rel-func-params" -> applyRefactoring f a fl relFuncParams
  "remove-maybe" -> applyRefactoring f a fl removeMaybe
  _ -> err $ "Unknown refactoring: " ++ show n
runCompiler (Args (Refactor _) Flags {refactorName = Nothing}) = err "No refactoring name provided"

-- | Parse and check a file.
parseAndCheckFile :: String -> Flags -> InputT IO Program
parseAndCheckFile file flags = do
  when (verbose flags) $ msg $ "Parsing file " ++ file
  contents <- liftIO $ readFile file
  parsed <- handleParse err (parseProgram file contents)
  when (dumpParsed flags) $ msg $ "Parsed program:\n" ++ show parsed
  (checked, state) <- handleTc err (checkProgram parsed)
  when (verbose flags) $ msg "\nTypechecked program successfully"
  when (dumpParsed flags) $ msg $ "Parsed + checked program:\n" ++ show checked
  when (verbose flags) $ msg $ "\nEnding state:\n" ++ show state
  return checked

-- | Apply a refactoring to a file.
applyRefactoring :: (FromRefactorArgs a) => String -> RefactorArgs -> Flags -> (a -> Program -> Refact Program) -> InputT IO ()
applyRefactoring f args flags r = do
  program <- parseAndCheckFile f flags
  when (verbose flags) $ msg $ "Applying refactoring to file " ++ f
  args' <- case fromRefactorArgs args of
    Nothing -> err "Failed to parse refactoring arguments"
    Just a -> return a
  let refactored = evalRefact (r args' program)
  when (verbose flags) $ msg "Refactored program"
  case applyChanges flags of
    InPlace -> liftIO $ writeFile f (show refactored)
    Print -> msg $ show refactored
    NewFile -> liftIO $ writeFile ("refactored_" ++ f) (show refactored)

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
handleTc :: (String -> InputT IO (a, TcState)) -> Tc a -> InputT IO (a, TcState)
handleTc er a = do
  case runTc a of
    Left e -> er $ "Error: " ++ show e
    Right (p, s) -> return (p, s)
