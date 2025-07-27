-- In Parser.hs in Haskell library
module Parser where

import Text.Megaparsec …

data TypeA c = VarA (Maybe Int) | ConstA -- unused?

data ExprA c = DomainA (ExprAtom c)
data EqA c = EqA (ExprA c) (ExprA c)

data AtomA c = AtomA String [ExprA c]
data LiteralA c = AtomLit (AtomA c) | EqLit (EqA c)
data ClauseA c = ClauseA (AtomA c) [LiteralA c]

type Parser = Parsec Void String

parseExpr :: Parser (ExprA c)
parseExpr = undefined -- parse domainExpr

parseAtom :: Parser (AtomA c)
parseAtom = do
  name <- some letterChar
  args <- between (char '(') (char ')') (parseExpr `sepBy` char ',')
  return $ AtomA name args

parseLiteral :: Parser (LiteralA c)
parseLiteral = try (EqLit <$> ((EqA <$> parseExpr <*> (string "=ℒ" *> parseExpr))))
            <|> (AtomLit <$> parseAtom)

parseClause :: Parser (ClauseA c)
parseClause = do
  hd <- parseAtom
  body <- optional (string ":-" *> parseLiteral `sepBy1` char ',')
  void $ char '.'
  return $ ClauseA hd (maybe [] id body)
