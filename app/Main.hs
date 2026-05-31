{-# OPTIONS_GHC -O2 #-}

module Main (main) where

import MAlonzo.Code.Examples.QgraphColoring
import MAlonzo.Code.Examples.QtravelingSalesman
import MAlonzo.Code.Examples.Qhanoi_without_fd
import FDSolver
import Data.Text
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [problem, diffStr] ->
      case (problem, diffStr) of
        ("graphColoring", "1") -> run gcExecute1
        ("graphColoring", "2") -> run gcExecute2
        ("graphColoring", "3") -> run gcExecute3

        ("travelingSalesman", "1") -> run tsExecute1
        ("travelingSalesman", "2") -> run tsExecute2
        ("travelingSalesman", "3") -> run tsExecute3

        ("hanoi", "1") -> run hExecute1
        ("hanoi", "2") -> run hExecute2
        ("hanoi", "3") -> run hExecute3

        _ -> usage

    _ -> usage

-- helper to keep your original printing logic
run :: [Text] -> IO ()
run = mapM_ (putStrLn . unpack)

-- usage output
usage :: IO ()
usage = putStrLn $
  "Usage: <program> (graphColoring|travelingSalesman|hanoi) (1|2|3)"