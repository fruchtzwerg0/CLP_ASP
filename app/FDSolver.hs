module FDSolver
  ( Var
  , Expr(..)
  , Constraint(..)
  , Store
  , isSatisfiable
  , labeling
  ) where

import System.IO
import System.Process
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import Data.List (intercalate, nub)
import Data.Maybe (mapMaybe)

type Var = String

data Expr
  = Lit Int
  | Var Var
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | Div Expr Expr
  deriving (Show)

data Constraint
  = Lt  Expr Expr   -- 
  | Gt  Expr Expr   -- >
  | Leq Expr Expr   -- <=
  | Geq Expr Expr   -- >=
  | Eq  Expr Expr   -- =
  | Neq Expr Expr   -- \=
  deriving (Show)

type Store = [Constraint]

data SolverProcess = SolverProcess
  { solverIn  :: Handle
  , solverOut :: Handle
  }

solverRef :: IORef (Maybe SolverProcess)
solverRef = unsafePerformIO (newIORef Nothing)
{-# NOINLINE solverRef #-}

getSolver :: IO SolverProcess
getSolver = do
  ms <- readIORef solverRef
  case ms of
    Just s  -> return s
    Nothing -> do
      (Just hin, Just hout, _, _) <- createProcess
        (proc "swipl" ["-q", "-t", "halt", "-f", "/dev/stdin"])
          { std_in  = CreatePipe
          , std_out = CreatePipe
          , std_err = NoStream
          }
      hSetBuffering hin  LineBuffering
      hSetBuffering hout LineBuffering

      hPutStrLn hin ":- use_module(library(clpfd))."
      hPutStrLn hin ":- use_module(library(lists))."

      let s = SolverProcess hin hout
      writeIORef solverRef (Just s)
      return s

renderExpr :: Expr -> String
renderExpr (Lit n)     = show n
renderExpr (Var v)     = v
renderExpr (Add a b)   = "(" ++ renderExpr a ++ " + " ++ renderExpr b ++ ")"
renderExpr (Sub a b)   = "(" ++ renderExpr a ++ " - " ++ renderExpr b ++ ")"
renderExpr (Mul a b)   = "(" ++ renderExpr a ++ " * " ++ renderExpr b ++ ")"
renderExpr (Div a b)   = "(" ++ renderExpr a ++ " // " ++ renderExpr b ++ ")"

renderConstraint :: Constraint -> String
renderConstraint (Lt  a b) = renderExpr a ++ " #< "  ++ renderExpr b
renderConstraint (Gt  a b) = renderExpr a ++ " #> "  ++ renderExpr b
renderConstraint (Leq a b) = renderExpr a ++ " #=< " ++ renderExpr b
renderConstraint (Geq a b) = renderExpr a ++ " #>= " ++ renderExpr b
renderConstraint (Eq  a b) = renderExpr a ++ " #= "  ++ renderExpr b
renderConstraint (Neq a b) = renderExpr a ++ " #\\= " ++ renderExpr b

collectVars :: Store -> [Var]
collectVars = nub . concatMap cvC
  where
    cvC (Lt  a b) = cvE a ++ cvE b
    cvC (Gt  a b) = cvE a ++ cvE b
    cvC (Leq a b) = cvE a ++ cvE b
    cvC (Geq a b) = cvE a ++ cvE b
    cvC (Eq  a b) = cvE a ++ cvE b
    cvC (Neq a b) = cvE a ++ cvE b
    cvE (Var v)   = [v]
    cvE (Lit _)   = []
    cvE (Add a b) = cvE a ++ cvE b
    cvE (Sub a b) = cvE a ++ cvE b
    cvE (Mul a b) = cvE a ++ cvE b
    cvE (Div a b) = cvE a ++ cvE b

capVar :: Var -> Var
capVar []     = []
capVar (c:cs) = toUpperChar c : cs
  where
    toUpperChar x
      | x >= 'a' && x <= 'z' = toEnum (fromEnum x - 32)
      | otherwise             = x

capitaliseStore :: Store -> Store
capitaliseStore = map capC
  where
    capC (Lt  a b) = Lt  (capE a) (capE b)
    capC (Gt  a b) = Gt  (capE a) (capE b)
    capC (Leq a b) = Leq (capE a) (capE b)
    capC (Geq a b) = Geq (capE a) (capE b)
    capC (Eq  a b) = Eq  (capE a) (capE b)
    capC (Neq a b) = Neq (capE a) (capE b)
    capE (Var v)   = Var (capVar v)
    capE (Lit n)   = Lit n
    capE (Add a b) = Add (capE a) (capE b)
    capE (Sub a b) = Sub (capE a) (capE b)
    capE (Mul a b) = Mul (capE a) (capE b)
    capE (Div a b) = Div (capE a) (capE b)

buildQuery :: Store -> [Var] -> String -> String
buildQuery store vars mode =
  let constraints = intercalate ", " (map renderConstraint store)
      varList     = "[" ++ intercalate "," vars ++ "]"
      domainGoal  = varList ++ " ins -1000000..1000000"
      labelGoal   = "label(" ++ varList ++ ")"
      printGoals  = intercalate ", " (map printGoal vars)
      printGoal v = "format('~w=~w~n', ['" ++ v ++ "', " ++ v ++ "])"
      body = case mode of
        "sat"   -> intercalate ", " [domainGoal, constraints]
        _       -> intercalate ", " [domainGoal, constraints, labelGoal, printGoals]
  in  "( " ++ body ++ " -> write('__SAT__') ; write('__UNSAT__') ), write('__END__'), nl."

readUntilEnd :: Handle -> IO [String]
readUntilEnd h = go []
  where
    go acc = do
      line <- hGetLine h
      if "__END__" `elem` words' line
        then return (reverse acc)
        else go (line : acc)
    words' s = [s]

runQuery :: Store -> String -> IO (Bool, [(Var, Int)])
runQuery rawStore mode = do
  let store = capitaliseStore rawStore
      vars  = collectVars store
  solver <- getSolver
  let query = buildQuery store vars mode
  hPutStrLn (solverIn solver) query
  hFlush    (solverIn solver)
  ls <- readUntilEnd (solverOut solver)
  let allOutput = unwords ls ++ " " ++ intercalate " " ls
      sat        = "__SAT__" `elem` concatMap splitTokens ls
      bindings   = if sat && mode == "label"
                   then mapMaybe parseBinding ls
                   else []
  return (sat, bindings)
  where
    splitTokens s = words s

parseBinding :: String -> Maybe (Var, Int)
parseBinding s =
  case break (== '=') s of
    (v, '=' : rest) -> case reads rest of
      [(n, "")] -> Just (v, n)
      _         -> Nothing
    _ -> Nothing

isSatisfiable :: Store -> IO Bool
isSatisfiable store = fst <$> runQuery store "sat"

labeling :: Store -> IO (Maybe [(Var, Int)])
labeling store = do
  (sat, bindings) <- runQuery store "label"
  return $ if sat then Just bindings else Nothing