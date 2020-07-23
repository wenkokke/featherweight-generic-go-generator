{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Concurrent (forkFinally)
import Control.Concurrent.MVar
import Control.Monad (forM, forM_)
import Control.Search
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
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.IO (stderr)
import System.IO.Temp (withSystemTempDirectory)
import System.Process (readProcessWithExitCode)
import System.ProgressBar


-- * Main function

maxDepth :: Int
maxDepth = 15

batchSize :: Int
batchSize = 100

fgg :: [String] -> IO (ExitCode, String, String)
fgg args = readProcessWithExitCode "go" ("run" : "github.com/rhu1/fgg" : args) ""

type ErrorMsg = Text

test_monomCommute :: DB.Prog ann -> IO (Maybe ErrorMsg)
test_monomCommute prog = do
  let progSrc = N.prettyProg (DB.convProg prog)
  withSystemTempDirectory "fgg" $ \tmpDir -> do
    let tmpPath = tmpDir </> "main.fgg"
    T.writeFile tmpPath progSrc
    (exitCode, stdout, stderr) <- fgg ["-eval=-1", "-test-monom", tmpPath]
    case exitCode of
      ExitSuccess -> return Nothing
      _           -> return . Just . T.unlines $
        [ "Source:" , progSrc , "Output:" , T.pack stdout , "Errors:" , T.pack stderr ]

wellTypedProgs :: Int -> IO [DB.Prog ()]
wellTypedProgs depth = search' O depth (DB.checkProg' opts)
  where
    opts = DB.TCSOpts
      { DB.optMethMin     = Just 1
      , DB.optFldMin      = Just 1
      , DB.optEmptyStrMax = Just 2
      , DB.optEmptyIntMax = Just 1
      }

main :: IO ()
main = do
  -- Get the number of CPUs available
  numProcessors <- getNumProcessors

  -- Divvy the well-typed programs up into batches
  batches <- chunksOf batchSize <$> wellTypedProgs maxDepth
  forM_ (zip [1 :: Int ..] batches) $ \(batchNum, batch) -> do

    -- Create a progress bar
    let style = defStyle { stylePrefix = msg ("Batch #" <> TL.pack (show batchNum)) }
    pb <- newProgressBar style 10 (Progress 0 batchSize ())

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
