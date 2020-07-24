{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Concurrent (forkFinally)
import Control.Concurrent.MVar
import Control.Monad (forM, forM_)
import qualified Control.Search as NEAT
import Data.List (transpose)
import Data.List.Split (chunksOf)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as TL
import Data.Maybe (catMaybes)
import GHC.Conc (getNumProcessors)
import qualified Language.FGG.DeBruijn as DB
import qualified Language.FGG.Named as N
import System.Console.GetOpt
import System.Environment (getArgs)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.IO (stdout,stderr)
import System.IO.Temp (withSystemTempDirectory)
import System.Process (readProcessWithExitCode)
import System.ProgressBar


-- * Main function

data Options = Options
  { maxDepth     :: Int
  , batchSize    :: Int
  , numProcesses :: Maybe Int
  , goCmd        :: String
  , goArgs       :: [String]
  } deriving Show

defaultOptions :: Options
defaultOptions = Options
  { maxDepth     = 15
  , batchSize    = 100
  , numProcesses = Nothing
  , goCmd        = "go"
  , goArgs       = ["run", "github.com/rhu1/fgg", "-eval=-1", "-test-monom"]
  }

options :: [OptDescr (Options -> Options)]
options =
  [ Option ['d'] ["max-depth"]
    (ReqArg (\arg opts -> opts { maxDepth = read arg }) "NUM")
    "search depth"
  , Option ['b'] ["batch-size"]
    (ReqArg (\arg opts -> opts { batchSize = read arg }) "NUM")
    "number of tasks allocated to each thread"
  , Option ['J'] ["num-processes"]
    (ReqArg (\arg opts -> opts { numProcesses = Just . read $ arg }) "NUM")
    "number of processors to use"
  , Option [] ["go-cmd"]
    (ReqArg (\arg opts -> opts { goCmd = arg }) "PATH")
    "path to go executable"
  , Option [] ["go-arg"]
    (ReqArg (\arg opts -> opts { goArgs = goArgs opts ++ [arg] }) "ARG")
    "arguments for go executable"
  ]

fgg :: [String] -> IO (ExitCode, String, String)
fgg args = readProcessWithExitCode "go" ("run" : "github.com/rhu1/fgg" : args) ""

type ErrorMsg = Text

test_monomCommute :: DB.Prog ann -> IO (Maybe ErrorMsg)
test_monomCommute prog = do
  let progSrc = N.prettyProg (DB.convProg prog)
  withSystemTempDirectory "fgg" $ \tmpDir -> do
    let tmpPath = tmpDir </> "main.fgg"
    T.writeFile tmpPath progSrc
    (exitCode, fggout, fggerr) <- fgg ["-eval=-1", "-test-monom", tmpPath]
    case exitCode of
      ExitSuccess -> return Nothing
      _           -> return . Just . T.unlines $
        [ "Source:" , progSrc , "Output:" , T.pack fggout , "Errors:" , T.pack fggerr ]

wellTypedProgs :: Int -> IO [DB.Prog ()]
wellTypedProgs depth = NEAT.search' NEAT.O depth (DB.checkProg' opts)
  where
    opts = DB.TCSOpts
      { DB.optMethMin     = Just 1
      , DB.optFldMin      = Just 1
      , DB.optEmptyStrMax = Just 2
      , DB.optEmptyIntMax = Just 1
      }

parseOpts :: [String] -> IO (Options, [String])
parseOpts argv =
  case getOpt Permute options argv of
    (o,n,[]  ) -> return (foldl (flip id) defaultOptions o, n)
    (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
  where header = "Usage: fgg-gen [OPTION...]"

main :: IO ()
main = do

  -- Parse command-line arguments
  (Options{..}, _) <- parseOpts =<< getArgs

  -- Get the number of processes (or the number of processors)
  numProcessors <- maybe getNumProcessors return numProcesses

  -- Divvy the well-typed programs up into batches
  batches <- chunksOf batchSize <$> wellTypedProgs maxDepth
  forM_ (zip [1 :: Int ..] batches) $ \(batchNum, batch) -> do

    -- Create a progress bar
    let style = defStyle { stylePrefix = msg ("Batch #" <> TL.pack (show batchNum)) }
    pb <- hNewProgressBar stdout style 10 (Progress 0 batchSize ())

    -- Divvy up the work amongst CPUs
    let subBatches = transpose (chunksOf numProcessors batch)
    ts <- forM subBatches $ \subBatch -> do

      -- Create an MVar to signal completion
      t <- newEmptyMVar :: IO (MVar [ErrorMsg])

      -- Create worker thread
      _ <- forkFinally
           (forM subBatch $ \prog -> do
               merrMsg <- test_monomCommute prog
               incProgress pb 1
               return merrMsg)
           (\case
               Left  err     -> putMVar t [T.pack . show $ err]
               Right merrLog -> putMVar t (catMaybes merrLog))
      return t

    -- Wait for all worker threads to finish
    forM_ ts $ \t -> do
      errLog <- takeMVar t
      forM_ errLog (T.hPutStrLn stderr)
