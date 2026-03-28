module Main (main) where


import MAlonzo.Code.Examples.Qstreamreasoning
import FDSolver
import Data.Text (pack, unpack)

main :: IO ()
main = do
  let answer = d_getDuals_126
{-
main :: IO ()
main = do
  let store =
        [ Geq (Var (pack "X")) (Lit 1)
        , Leq (Var (pack "X")) (Lit 10)
        , Geq (Var (pack "Y")) (Lit 1)
        , Leq (Var (pack "Y")) (Lit 10)
        , Eq  (Add (Var (pack "X")) (Var (pack "Y"))) (Lit 7)
        , Lt  (Var (pack "X")) (Var (pack "Y"))
        ]

  sat <- isSatisfiable store
  putStrLn $ "Satisfiable: " ++ show sat

  result <- labeling store
  case result of
    Nothing -> putStrLn "No solution."
    Just bs -> mapM_ (\b -> putStrLn $ unpack (var b) ++ " = " ++ show (val b)) bs
-}