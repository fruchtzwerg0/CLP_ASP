{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module FDSolver
  ( Binding(..), Expr(..), Constraint(..), Store
  , isSatisfiable, labeling
  ) where

import Control.Concurrent   (forkIO)
import Control.Exception    (catch, IOException, SomeException)
import Control.Monad        (forever)
import Data.IORef
import Data.List            (intercalate, nub, isInfixOf)
import Data.Maybe           (mapMaybe)
import Data.Text            (Text, unpack, pack)
import qualified Data.Text  as T
import System.IO
import System.IO.Unsafe     (unsafePerformIO)
import System.Process

data Binding = MkBinding { var :: Text, val :: Integer } deriving (Show, Eq)
type Store   = [Constraint]

data Expr
  = Lit Integer | Var Text
  | Add Expr Expr | Sub Expr Expr | Mul Expr Expr | Div Expr Expr
  deriving Show

data Constraint
  = Lt Expr Expr | Gt Expr Expr | Leq Expr Expr
  | Geq Expr Expr | Eq Expr Expr | Neq Expr Expr
  deriving Show

-- ── solver process ────────────────────────────────────────────────────────────

data SolverProcess = SolverProcess { solverIn :: Handle, solverOut :: Handle }

solverRef :: IORef (Maybe SolverProcess)
solverRef = unsafePerformIO (newIORef Nothing)
{-# NOINLINE solverRef #-}

getSolver :: IO SolverProcess
getSolver = do
  ms <- readIORef solverRef
  case ms of
    Just s  -> return s
    Nothing -> do
      (Just hin, Just hout, Just herr, _) <- createProcess
        (proc "swipl" ["-q", "--traditional"])
          { std_in  = CreatePipe
          , std_out = CreatePipe
          , std_err = CreatePipe   -- must drain stderr or it blocks
          }
      hSetBuffering hin  LineBuffering
      hSetBuffering hout LineBuffering
      hSetBuffering herr NoBuffering

      -- Drain stderr in the background so it never fills the OS pipe buffer
      _ <- forkIO $ forever (hGetLine herr >> return ())
             `catch` (\(_ :: IOException) -> return ())

      -- Load modules and emit a sentinel we can wait for
      hPutStrLn hin ":- use_module(library(clpfd)), \
                     \use_module(library(lists)), \
                     \write('__READY__'), nl."
      hFlush hin
      drainUntil hout "__READY__"   -- consume startup output

      let s = SolverProcess hin hout
      writeIORef solverRef (Just s)
      return s

-- ── I/O helpers ──────────────────────────────────────────────────────────────

-- Read lines until one contains `sentinel` (use isInfixOf, not `elem` words,
-- so it works even when Prolog prints two tokens on the same line).
drainUntil :: Handle -> String -> IO [String]
drainUntil h sentinel = go []
  where
    go acc = do
      line <- hGetLine h
      if sentinel `isInfixOf` line
        then return (reverse acc)
        else go (line : acc)

-- ── rendering ────────────────────────────────────────────────────────────────

renderExpr :: Expr -> String
renderExpr (Lit n)   = show n
renderExpr (Var v)   = unpack v
renderExpr (Add a b) = "(" ++ renderExpr a ++ " + "   ++ renderExpr b ++ ")"
renderExpr (Sub a b) = "(" ++ renderExpr a ++ " - "   ++ renderExpr b ++ ")"
renderExpr (Mul a b) = "(" ++ renderExpr a ++ " * "   ++ renderExpr b ++ ")"
renderExpr (Div a b) = "(" ++ renderExpr a ++ " // "  ++ renderExpr b ++ ")"

renderConstraint :: Constraint -> String
renderConstraint (Lt  a b) = renderExpr a ++ " #< "   ++ renderExpr b
renderConstraint (Gt  a b) = renderExpr a ++ " #> "   ++ renderExpr b
renderConstraint (Leq a b) = renderExpr a ++ " #=< "  ++ renderExpr b
renderConstraint (Geq a b) = renderExpr a ++ " #>= "  ++ renderExpr b
renderConstraint (Eq  a b) = renderExpr a ++ " #= "   ++ renderExpr b
renderConstraint (Neq a b) = renderExpr a ++ " #\\= " ++ renderExpr b

-- ── variable collection & capitalisation ─────────────────────────────────────

collectVars :: Store -> [Text]
collectVars = nub . concatMap cvC
  where
    cvC c = case c of
      Lt  a b -> cvE a ++ cvE b; Gt  a b -> cvE a ++ cvE b
      Leq a b -> cvE a ++ cvE b; Geq a b -> cvE a ++ cvE b
      Eq  a b -> cvE a ++ cvE b; Neq a b -> cvE a ++ cvE b
    cvE (Var v)   = [v]
    cvE (Lit _)   = []
    cvE (Add a b) = cvE a ++ cvE b; cvE (Sub a b) = cvE a ++ cvE b
    cvE (Mul a b) = cvE a ++ cvE b; cvE (Div a b) = cvE a ++ cvE b

capVar :: Text -> Text
capVar t = case T.uncons t of
  Just (c, cs) -> T.cons (up c) cs
  Nothing      -> t
  where up x = if x >= 'a' && x <= 'z' then toEnum (fromEnum x - 32) else x

capitaliseStore :: Store -> Store
capitaliseStore = map capC
  where
    capC (Lt  a b) = Lt  (capE a) (capE b); capC (Gt  a b) = Gt  (capE a) (capE b)
    capC (Leq a b) = Leq (capE a) (capE b); capC (Geq a b) = Geq (capE a) (capE b)
    capC (Eq  a b) = Eq  (capE a) (capE b); capC (Neq a b) = Neq (capE a) (capE b)
    capE (Var v)   = Var (capVar v)
    capE (Lit n)   = Lit n
    capE (Add a b) = Add (capE a) (capE b); capE (Sub a b) = Sub (capE a) (capE b)
    capE (Mul a b) = Mul (capE a) (capE b); capE (Div a b) = Div (capE a) (capE b)

-- ── query building ───────────────────────────────────────────────────────────

buildQuery :: Store -> [Text] -> String -> String
buildQuery store vars mode =
  let constraints = intercalate ", " (map renderConstraint store)
      varList     = "[" ++ intercalate "," (map unpack vars) ++ "]"
      domainGoal  = varList ++ " ins -1000000..1000000"
      labelGoal   = "label(" ++ varList ++ ")"
      printGoals  = intercalate ", " (map printGoal vars)
      printGoal v = "format('~w=~w~n', ['" ++ unpack v ++ "', " ++ unpack v ++ "])"
      body = case mode of
        "sat" -> intercalate ", " [domainGoal, constraints]
        _     -> intercalate ", " [domainGoal, constraints, labelGoal, printGoals]
  in "( " ++ body ++ " -> write('__SAT__') ; write('__UNSAT__') ), write('__END__'), nl."

-- ── public API ───────────────────────────────────────────────────────────────

parseBinding :: String -> Maybe Binding
parseBinding s = case break (== '=') s of
  (v, '=' : rest) -> case reads rest of
    [(n, "")] -> Just (MkBinding (pack v) (fromIntegral (n :: Int)))
    _         -> Nothing
  _ -> Nothing

runQuery :: Store -> String -> IO (Bool, [Binding])
runQuery rawStore mode = do
  let store = capitaliseStore rawStore
      vars  = collectVars store
  solver <- getSolver
  let query = buildQuery store vars mode
  hPutStrLn (solverIn solver) query
  hFlush    (solverIn solver)
  ls <- drainUntil (solverOut solver) "__END__"
  let sat      = any ("__SAT__" `isInfixOf`) ls || "__SAT__" `isInfixOf` concat ls
      bindings = if sat && mode == "label"
                   then mapMaybe parseBinding ls
                   else []
  return (sat, bindings)

isSatisfiable :: Store -> IO Bool
isSatisfiable store = fst <$> runQuery store "sat"

labeling :: Store -> IO (Maybe [Binding])
labeling store = do
  (sat, bindings) <- runQuery store "label"
  return $ if sat then Just bindings else Nothing