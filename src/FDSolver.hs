{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module FDSolver
  ( Binding(..), Expr(..), Constraint(..), Store
  , isSatisfiable, labeling
  ) where

import Control.Concurrent   (forkIO)
import Control.Exception    (catch, IOException)
import Control.Monad        (forever)
import Data.IORef
import Data.List            (intercalate, nub, isInfixOf)
import Data.Maybe           (mapMaybe)
import Data.Text            (Text, unpack, pack)
import qualified Data.Text  as T
import System.IO
import System.IO.Unsafe     (unsafePerformIO)
import System.Process

data Binding = MkBinding { var :: Integer, val :: Integer } deriving (Show, Eq)
type Store   = [Constraint]

data Expr
  = Lit Integer | Var Integer         -- Var now holds an Integer index
  | Add Expr Expr | Sub Expr Expr | Mul Expr Expr | Div Expr Expr
  deriving Show

data Constraint
  = Lt Expr Expr | Gt Expr Expr | Leq Expr Expr
  | Geq Expr Expr | Eq Expr Expr | Neq Expr Expr
  deriving Show

-- ── var name encoding ─────────────────────────────────────────────────────────

-- Integer index → Prolog variable name  (must start with uppercase)
varName :: Integer -> String
varName n = "Var" ++ show n

-- Prolog variable name → Integer index  ("Var42" → Just 42)
parseVarName :: String -> Maybe Integer
parseVarName s
  | take 3 s == "Var" = case reads (drop 3 s) of
      [(n, "")] -> Just n
      _         -> Nothing
  | otherwise = Nothing

-- ── solver process ────────────────────────────────────────────────────────────

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
      --hPutStrLn stderr "[DEBUG] Spawning swipl..."
      (Just hin, Just hout, Just herr, _) <- createProcess
        (proc "swipl"
          [ "-q"
          , "--tty=false"
          , "-g", "use_module(library(clpfd))"
          , "-g", "use_module(library(lists))"
          , "-g", "set_prolog_flag(answer_write_options,[quoted(true)])"
          ])
          { std_in  = CreatePipe
          , std_out = CreatePipe
          , std_err = CreatePipe
          }
      hSetBuffering hin  LineBuffering
      hSetBuffering hout LineBuffering
      hSetEncoding  hin  utf8
      hSetEncoding  hout utf8
      hSetBuffering herr NoBuffering

      _ <- forkIO $ forever (hGetLine herr >>= \l ->
                      hPutStrLn stderr ("[SWIPL STDERR] " ++ l))
             `catch` (\(_ :: IOException) -> return ())

      --hPutStrLn stderr "[DEBUG] Sending ready probe..."
      hPutStrLn hin "write('__READY__'), nl."
      hFlush hin
      --hPutStrLn stderr "[DEBUG] Waiting for __READY__..."
      ls <- drainUntil hout "__READY__"
      --hPutStrLn stderr $ "[DEBUG] Got ready lines: " ++ show ls

      let s = SolverProcess hin hout
      writeIORef solverRef (Just s)
      --hPutStrLn stderr "[DEBUG] swipl ready."
      return s

-- ── I/O helpers ───────────────────────────────────────────────────────────────

drainUntil :: Handle -> String -> IO [String]
drainUntil h sentinel = go []
  where
    go acc = do
      line <- hGetLine h
      --hPutStrLn stderr $ "[DEBUG] < " ++ line
      if sentinel `isInfixOf` line
        then return (reverse (line : acc))
        else go (line : acc)

-- ── rendering ─────────────────────────────────────────────────────────────────

renderExpr :: Expr -> String
renderExpr (Lit n)   = show n
renderExpr (Var n)   = varName n          -- Integer → "VarN"
renderExpr (Add a b) = "(" ++ renderExpr a ++ "+"  ++ renderExpr b ++ ")"
renderExpr (Sub a b) = "(" ++ renderExpr a ++ "-"  ++ renderExpr b ++ ")"
renderExpr (Mul a b) = "(" ++ renderExpr a ++ "*"  ++ renderExpr b ++ ")"
renderExpr (Div a b) = "(" ++ renderExpr a ++ "//" ++ renderExpr b ++ ")"

renderConstraint :: Constraint -> String
renderConstraint (Lt  a b) = renderExpr a ++ " #< "   ++ renderExpr b
renderConstraint (Gt  a b) = renderExpr a ++ " #> "   ++ renderExpr b
renderConstraint (Leq a b) = renderExpr a ++ " #=< "  ++ renderExpr b
renderConstraint (Geq a b) = renderExpr a ++ " #>= "  ++ renderExpr b
renderConstraint (Eq  a b) = renderExpr a ++ " #= "   ++ renderExpr b
renderConstraint (Neq a b) = renderExpr a ++ " #\\= " ++ renderExpr b

-- ── variable collection ───────────────────────────────────────────────────────

-- Collect unique Integer indices from all Var nodes
collectVarIds :: Store -> [Integer]
collectVarIds = nub . concatMap cvC
  where
    cvC (Lt  a b) = cvE a ++ cvE b
    cvC (Gt  a b) = cvE a ++ cvE b
    cvC (Leq a b) = cvE a ++ cvE b
    cvC (Geq a b) = cvE a ++ cvE b
    cvC (Eq  a b) = cvE a ++ cvE b
    cvC (Neq a b) = cvE a ++ cvE b
    cvE (Var n)   = [n]
    cvE (Lit _)   = []
    cvE (Add a b) = cvE a ++ cvE b
    cvE (Sub a b) = cvE a ++ cvE b
    cvE (Mul a b) = cvE a ++ cvE b
    cvE (Div a b) = cvE a ++ cvE b

-- ── query building ────────────────────────────────────────────────────────────

buildQuery :: Store -> [Integer] -> String -> String
buildQuery store varIds mode =
  let constraints = intercalate ", " (map renderConstraint store)
      varNames    = map varName varIds
      varList     = "[" ++ intercalate "," varNames ++ "]"
      domainGoal  = varList ++ " ins -1000000..1000000"
      labelGoal   = "label(" ++ varList ++ ")"
      printGoals  = intercalate ", " (map printGoal varNames)
      printGoal v = "format('~w=~w~n', ['" ++ v ++ "', " ++ v ++ "])"
      body = case mode of
        "sat" -> intercalate ", " [domainGoal, constraints]
        _     -> intercalate ", " [domainGoal, constraints, labelGoal, printGoals]
  in "( " ++ body ++ " -> write('__SAT__') ; write('__UNSAT__') ), write('__END__'), nl."

-- ── parsing ───────────────────────────────────────────────────────────────────

-- Parse "Var42=7" → Just (MkBinding 42 7)
parseBinding :: String -> Maybe Binding
parseBinding s = case break (== '=') s of
  (v, '=' : rest) ->
    case (parseVarName v, reads rest) of
      (Just idx, [(n, "")]) -> Just (MkBinding idx (fromIntegral (n :: Int)))
      _                     -> Nothing
  _ -> Nothing

-- ── running ───────────────────────────────────────────────────────────────────

runQuery :: Store -> String -> IO (Bool, [Binding])
runQuery store mode = do
  let varIds = collectVarIds store
      query  = buildQuery store varIds mode
  --hPutStrLn stderr $ "[DEBUG] Mode: " ++ mode
  --hPutStrLn stderr $ "[DEBUG] Query: " ++ query
  solver <- getSolver
  hPutStrLn (solverIn solver) query
  hFlush    (solverIn solver)
  --hPutStrLn stderr "[DEBUG] Query sent, draining..."
  ls <- drainUntil (solverOut solver) "__END__"
  --hPutStrLn stderr $ "[DEBUG] All lines: " ++ show ls
  let allOutput = concat ls
      sat       = "__SAT__" `isInfixOf` allOutput
      bindings  = if sat && mode == "label"
                    then mapMaybe parseBinding ls
                    else []
  return (sat, bindings)

isSatisfiable :: Store -> IO Bool
isSatisfiable store = fst <$> runQuery store "sat"

labeling :: Store -> IO (Maybe [Binding])
labeling store = do
  (sat, bindings) <- runQuery store "label"
  return $ if sat then Just bindings else Nothing