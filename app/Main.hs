{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Concurrent (forkFinally)
import Control.Concurrent.MVar
import Control.Monad (forM,forM_,when,unless)
import qualified Control.Search as NEAT
import Data.List (transpose)
import Data.List.Split (chunksOf)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Maybe (catMaybes)
import GHC.Conc (getNumProcessors)
import qualified Language.FGG.DeBruijn.Size as DB
import qualified Language.FGG.DeBruijn as DB
import qualified Language.FGG.Named as N
import System.Console.GetOpt
import System.Directory (removeFile)
import System.Environment (getArgs)
import System.Exit (ExitCode(..),exitSuccess)
import System.IO (stdout,stderr)
import System.IO.Temp (writeSystemTempFile)
import System.Process (readProcessWithExitCode,showCommandForUser)
import qualified System.ProgressBar as PB
import Text.Printf


-- * Main function

data Verbosity
  = Quiet
  | Source
  | StepByStep
  deriving (Show,Eq,Ord)

data Options = Options
  { maxDepth     :: Int
  , maxSteps     :: Int
  , batchSize    :: Int
  , numProcesses :: Maybe Int
  , goCmd        :: String
  , goArgs       :: [String]
  , inline       :: Bool
  , verbosity    :: Verbosity
  , showHelp     :: Bool
  } deriving Show

defaultOptions :: Options
defaultOptions = Options
  { maxDepth     = 15
  , maxSteps     = 100
  , batchSize    = 100
  , numProcesses = Nothing
  , goCmd        = "go"
  , goArgs       = ["run", "github.com/rhu1/fgg", "-test-monom"]
  , inline       = True
  , verbosity    = Quiet
  , showHelp     = False
  }

options :: [OptDescr (Options -> Options)]
options =
  [ Option ['d'] ["max-depth"]
    (ReqArg (\arg opts -> opts { maxDepth = read arg }) "NUM")
    "Search depth (default is 15)."
  , Option ['n'] ["max-steps"]
    (ReqArg (\arg opts -> opts { maxSteps = read arg}) "NUM")
    "Maximum number of reduction steps (default is 100)."
  , Option ['b'] ["batch-size"]
    (ReqArg (\arg opts -> opts { batchSize = read arg }) "NUM")
    "Number of tasks allocated to each thread (default is 100)."
  , Option ['J'] ["num-processes"]
    (ReqArg (\arg opts -> opts { numProcesses = Just . read $ arg }) "NUM")
    "Number of processes to use (default is number of CPU cores)."
  , Option [] ["go-cmd"]
    (ReqArg (\arg opts -> opts { goCmd = arg }) "PATH")
    "Path to go executable."
  , Option [] ["go-args"]
    (ReqArg (\args opts -> opts { goArgs = words args }) "ARGS")
    "Arguments for go executable."
  , Option [] ["no-inline"]
    (NoArg (\opts -> opts { inline = True }))
    "Don't pass programs inline."
  , Option ['v'] []
    (NoArg (\opts -> opts { verbosity = Source }))
    "Show source, output, and error for all programs."
  , Option ['V'] []
    (NoArg (\opts -> opts { verbosity = StepByStep }))
    "As above, but also pass '-v' to go-cmd."
  , Option ['h'] ["help"]
    (NoArg (\opts -> opts { showHelp = True }))
    "Show this help."
  ]

fgg :: Options -> String -> IO (String, (ExitCode, String, String))
fgg Options{..} srcOrPath
  = fggWithArgs . concat $
    [ goArgs
    , [ "-eval=" <> show maxSteps ]
    , [ "-v" | verbosity >= StepByStep ]
    , [ "-inline" | inline ]
    , [ srcOrPath ]]
  where
    fggWithArgs args = do
      res <- readProcessWithExitCode goCmd args ""
      return (showCommandForUser goCmd args, res)

data Level
  = Debug
  | Error
  deriving (Show,Eq,Ord)

data Msg = Msg
  { msgLvl :: Level
  , msgTxt :: Text
  }

test_monomCommute :: Options -> DB.Prog ann -> IO (Maybe Msg)
test_monomCommute opts@Options{..} prog = do
  let src = N.prettyProg (DB.convProg prog)
  let srcStr = T.unpack src

  srcOrPath <-
        if inline then
          return srcStr
        else
          writeSystemTempFile "fgg" srcStr

  (cmd, (exitCode, out, err)) <- fgg opts srcOrPath

  unless inline $ removeFile srcOrPath

  let txt = T.unlines [ "Command:" , T.unwords . fmap T.strip . T.lines . T.pack $ cmd
                      , "Source:"  , src
                      , "Output:"  , T.pack out
                      , "Errors:"  , T.pack err ]

  return $ case exitCode of
             ExitSuccess -> if verbosity >= Source then Just (Msg Debug txt) else Nothing
             _           -> Just (Msg Error txt)

wellTypedProgs :: Int -> IO [DB.Prog ()]
wellTypedProgs depth = NEAT.search' NEAT.O depth (DB.checkProg' opts)
  where
    opts = DB.TCSOpts
      { DB.optMethMin     = Just 1
      , DB.optFldMin      = Just 1
      , DB.optEmptyStrMax = Just 2
      , DB.optEmptyIntMax = Just 1
      }

usageHeader :: String
usageHeader = "Usage: fgg-gen [OPTION...]\n"

parseOpts :: [String] -> IO (Options, [String])
parseOpts argv =
  case getOpt Permute options argv of
    (o,n,[]  ) -> return (foldl (flip id) defaultOptions o, n)
    (_,_,errs) -> ioError (userError (concat errs ++ usageInfo usageHeader options))

printMsg :: Msg -> IO ()
printMsg (Msg _ txt) = T.hPutStrLn stderr txt

main :: IO ()
main = do

  -- Parse command-line arguments
  opts@Options{..} <- fmap fst . parseOpts =<< getArgs

  -- Print the usage info and exit
  when showHelp $ do
    putStrLn (usageInfo usageHeader options)
    exitSuccess

  -- Get the number of processes (or the number of processors)
  numProcessors <- maybe getNumProcessors return numProcesses
  printf "Using %d processes\n" numProcessors

  -- Divvy the well-typed programs up into batches
  batches <- chunksOf batchSize <$> wellTypedProgs maxDepth
  forM_ (zip [1 :: Int ..] batches) $ \(batchNum, batch) -> do

    -- Print batch description
    unless (null batch) $ do
      let batchProgSizes = map DB.size batch
      printf "Batch %03d: %d programs, with sizes between %d and %d\n"
        batchNum
        (length batch)           -- Size of batch
        (minimum batchProgSizes) -- Size of smallest
        (maximum batchProgSizes) -- Size of largest

    -- Create a progress bar
    pb <- PB.hNewProgressBar stdout PB.defStyle 10 (PB.Progress 0 batchSize ())

    -- Divvy up the work amongst CPUs
    let subBatches = transpose (chunksOf numProcessors batch)
    ts <- forM subBatches $ \subBatch -> do

      -- Create an MVar to signal completion
      t <- newEmptyMVar :: IO (MVar [Msg])

      -- Create worker thread
      _ <- forkFinally
           (forM subBatch $ \prog -> do
               mmsgMsg <- test_monomCommute opts prog
               PB.incProgress pb 1
               return mmsgMsg)
           (\case
               Left  msg     -> putMVar t [Msg Error (T.pack . show $ msg)]
               Right mmsgLog -> putMVar t (catMaybes mmsgLog))
      return t

    -- Wait for all worker threads to finish
    forM_ ts $ \t -> do
      msgLog <- takeMVar t
      forM_ msgLog printMsg
