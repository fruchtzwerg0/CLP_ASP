module Lib
    ( someFunc
    ) where

someFunc :: IO ()
someFunc = putStrLn "someFunc"

data TypeA = Var (Maybe Int) | Const Atom
data TermA = ConstT String
           | AtomT String [TermA]
  deriving (Show, Eq)

data ClauseA = ClauseA TermA [TermA]
  deriving (Show, Eq)
