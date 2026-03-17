{-# LANGUAGE QuasiQuotes #-}
module Main (main) where


--import MAlonzo.Code.CLPtermHs

import FDSolver

main :: IO ()
main = do
  let store =
        [ Geq (Var "X") (Lit 1)
        , Leq (Var "X") (Lit 10)
        , Geq (Var "Y") (Lit 1)
        , Leq (Var "Y") (Lit 10)
        , Eq  (Add (Var "X") (Var "Y")) (Lit 7)
        , Lt  (Var "X") (Var "Y")
        ]

  sat <- isSatisfiable store
  putStrLn $ "Satisfiable: " ++ show sat

  result <- labeling store
  case result of
    Nothing -> putStrLn "No solution."
    Just bs -> mapM_ (\(v,n) -> putStrLn $ v ++ " = " ++ show n) bs