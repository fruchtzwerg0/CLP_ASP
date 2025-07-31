{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Parser (prologProgram, prologQuestion) where

import Data.Void (Void)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.Char (isLower, isUpper, isAlphaNum)
import Data.Data (cast)
import Control.Monad.State as S
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Language.Haskell.TH (Exp, Q)
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Language.Haskell.TH.Syntax (lift, dataToExpQ)
import MAlonzo.Code.CLPtermHs

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

atomIdentifier :: Parser String
atomIdentifier = lexeme ((:) <$> satisfy isLower <*> many (satisfy isAlphaNum))

varIdentifier :: Parser String
varIdentifier = lexeme ((:) <$> satisfy isUpper <*> many (satisfy isAlphaNum))

data RawTermHs
  = RawAtomTHs T.Text [RawTypeHs]
  deriving (Show, Eq)

data RawTypeHs
  = RawVarHs (Maybe String)
  | RawConstHs RawTermHs
  deriving (Show, Eq)

data RawExprTermHs = RawExprTermHs RawTypeHs deriving (Show, Eq)
data RawAtomTermHs = RawAtomTermHs T.Text [RawExprTermHs] deriving (Show, Eq)
data RawLiteralTermHs
  = RawEqLiteralTermHs RawExprTermHs RawExprTermHs
  | RawAtomLiteralTermHs RawAtomTermHs
  deriving (Show, Eq)

data RawClauseTermHs = RawClauseTermHs RawAtomTermHs [RawLiteralTermHs]
  deriving (Show, Eq)

pTypeRaw :: Parser RawTypeHs
pTypeRaw =
      (symbol "_" >> return (RawVarHs Nothing))
  <|> try (do
          name <- atomIdentifier
          args <- parens (pTypeRaw `sepBy` symbol ",")
          return $ RawConstHs (RawAtomTHs (T.pack name) args))
  <|> try (RawConstHs . (`RawAtomTHs` []) . T.pack <$> atomIdentifier)
  <|> (RawVarHs . Just <$> varIdentifier)


pExprTerm :: Parser RawExprTermHs
pExprTerm = RawExprTermHs <$> pTypeRaw

pAtomTerm :: Parser RawAtomTermHs
pAtomTerm = do
  name <- atomIdentifier
  args <- parens (pExprTerm `sepBy` symbol ",")
  return $ RawAtomTermHs (T.pack name) args

pEqTerm :: Parser (RawExprTermHs, RawExprTermHs)
pEqTerm = do
  e1 <- pExprTerm
  _ <- symbol "="
  e2 <- pExprTerm
  return (e1, e2)

pLiteralTerm :: Parser RawLiteralTermHs
pLiteralTerm =
  try (do (e1, e2) <- pEqTerm
          return $ RawEqLiteralTermHs e1 e2)
  <|> (RawAtomLiteralTermHs <$> pAtomTerm)

pClauseTerm :: Parser RawClauseTermHs
pClauseTerm = do
  hd <- pAtomTerm
  body <- optional (symbol ":-" *> (pLiteralTerm `sepBy1` symbol ","))
  _ <- optional (symbol ".")
  return $ RawClauseTermHs hd (maybe [] id body)

type VarMap = M.Map String Integer
type RenumberM = S.State (VarMap, Integer)

renumberRawClause :: RawClauseTermHs -> ClauseTermHs
renumberRawClause raw = evalState (goClause raw) (M.empty, 1)

goClause :: RawClauseTermHs -> RenumberM ClauseTermHs
goClause (RawClauseTermHs h b) = do
  h' <- goAtom h
  b' <- mapM goLit b
  return $ MkClauseTermHs h' b'

goLit :: RawLiteralTermHs -> RenumberM LiteralTermHs
goLit (RawAtomLiteralTermHs a) = AtomLiteralTermHs <$> goAtom a
goLit (RawEqLiteralTermHs e1 e2) =
  EqLiteralTermHs <$> (EqTermHs <$> goExpr e1 <*> goExpr e2)

goAtom :: RawAtomTermHs -> RenumberM AtomTermHs
goAtom (RawAtomTermHs name args) =
  MkAtomTermHs name <$> mapM goExpr args

goExpr :: RawExprTermHs -> RenumberM ExprTermHs
goExpr (RawExprTermHs t) = MkExprTermHs <$> goType t

goType :: RawTypeHs -> RenumberM LogicVarHs
goType (RawVarHs Nothing) = return $ MkVarHs Nothing
goType (RawVarHs (Just name)) = do
  (env, next) <- get
  case M.lookup name env of
    Just i  -> return $ MkVarHs (Just i)
    Nothing -> do
      let env' = M.insert name next env
      put (env', next + 1)
      return $ MkVarHs (Just next)
goType (RawConstHs t) = MkConstHs <$> goTerm t

goTerm :: RawTermHs -> RenumberM TermHs
goTerm (RawAtomTHs name args) = MkAtomTHs name <$> mapM goType args

quotePrologExp :: String -> Q Exp
quotePrologExp input =
  case parse (sc *> many pClauseTerm <* eof) "" input of
    Left err  -> fail (errorBundlePretty err)
    Right rawClauses ->
      let clauses = map renumberRawClause rawClauses
      in dataToExpQ (fmap liftText . cast) clauses
  where
    liftText :: T.Text -> Q Exp
    liftText = Language.Haskell.TH.Syntax.lift

quoteQuestionExp :: String -> Q Exp
quoteQuestionExp input =
  case parse (sc *> (pLiteralTerm `sepBy` symbol ",") <* eof) "" input of
    Left err  -> fail (errorBundlePretty err)
    Right rawLits ->
      let clause = RawClauseTermHs (RawAtomTermHs "query" []) rawLits
      in dataToExpQ (fmap liftText . cast) (clauseBody $ renumberRawClause clause)
  where
    clauseBody (MkClauseTermHs _ b) = b
    liftText :: T.Text -> Q Exp
    liftText = Language.Haskell.TH.Syntax.lift

prologProgram :: QuasiQuoter
prologProgram = QuasiQuoter
  { quoteExp  = quotePrologExp
  , quotePat  = undefined
  , quoteType = undefined
  , quoteDec  = undefined
  }

prologQuestion :: QuasiQuoter
prologQuestion = QuasiQuoter
  { quoteExp  = quoteQuestionExp
  , quotePat  = undefined
  , quoteType = undefined
  , quoteDec  = undefined
  }