{-# OPTIONS_GHC -O2 #-}

module Main (main) where


import MAlonzo.Code.Examples.Qhanoi
import FDSolver
import Data.Text (pack, unpack)

main :: IO ()
main = do
  print execute

{-
main :: IO ()
main = do
  let store =
        [ Geq (Var 0) (Lit 1)
        , Leq (Var 0) (Lit 10)
        , Geq (Var 1) (Lit 1)
        , Leq (Var 1) (Lit 10)
        , Eq  (Add (Var 0) (Var 1)) (Lit 7)
        , Lt  (Var 0) (Var 1)
        ]
  sat <- isSatisfiable store
  putStrLn $ "Satisfiable: " ++ show sat
  result <- labeling store
  case result of
    Nothing -> putStrLn "No solution."
    Just bs -> mapM_ (\b -> putStrLn $ "Var" ++ show (var b) ++ " = " ++ show (val b)) bs
-}