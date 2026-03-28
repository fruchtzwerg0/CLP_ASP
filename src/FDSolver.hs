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

-- ── types ────────────────────────────────────────────────────────────────────

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
      hPutStrLn stderr "[DEBUG] Spawning swipl..."
      -- Use -g to load modules before the toplevel starts,
      -- and --tty=false to disable any interactive prompt handling
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

      -- Drain stderr in background so it never blocks
      _ <- forkIO $ forever (hGetLine herr >>= \l ->
                      hPutStrLn stderr ("[SWIPL STDERR] " ++ l))
             `catch` (\(_ :: IOException) -> return ())

      -- Send a plain goal (no :-) to confirm the process is alive
      hPutStrLn stderr "[DEBUG] Sending ready probe..."
      hPutStrLn hin "write('__READY__'), nl."
      hFlush hin
      hPutStrLn stderr "[DEBUG] Waiting for __READY__..."
      ls <- drainUntil hout "__READY__"
      hPutStrLn stderr $ "[DEBUG] Got ready lines: " ++ show ls

      let s = SolverProcess hin hout
      writeIORef solverRef (Just s)
      hPutStrLn stderr "[DEBUG] swipl ready."
      return s

-- ── I/O helpers ──────────────────────────────────────────────────────────────

drainUntil :: Handle -> String -> IO [String]
drainUntil h sentinel = go []
  where
    go acc = do
      line <- hGetLine h
      hPutStrLn stderr $ "[DEBUG] < " ++ line
      if sentinel `isInfixOf` line
        then return (reverse (line : acc))  -- include the sentinel line
        else go (line : acc)

-- ── rendering ────────────────────────────────────────────────────────────────

renderExpr :: Expr -> String
renderExpr (Lit n)   = show n
renderExpr (Var v)   = unpack v
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

-- ── variable collection & capitalisation ─────────────────────────────────────

collectVars :: Store -> [Text]
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

capVar :: Text -> Text
capVar t = case T.uncons t of
  Just (c, cs) -> T.cons (up c) cs
  Nothing      -> t
  where up x = if x >= 'a' && x <= 'z' then toEnum (fromEnum x - 32) else x

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

-- ── query building ───────────────────────────────────────────────────────────
-- Note: no :- prefix — these are plain goals sent to the interactive toplevel

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

-- ── running ───────────────────────────────────────────────────────────────────

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
      query = buildQuery store vars mode
  hPutStrLn stderr $ "[DEBUG] Query: " ++ query
  solver <- getSolver
  hPutStrLn (solverIn solver) query
  hFlush    (solverIn solver)
  hPutStrLn stderr "[DEBUG] Query sent, draining..."
  ls <- drainUntil (solverOut solver) "__END__"
  hPutStrLn stderr $ "[DEBUG] All lines: " ++ show ls
  let allOutput = concat ls          -- check across the whole output, not line by line
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