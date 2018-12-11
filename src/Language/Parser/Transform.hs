module Language.Parser.Transform (transExpParser) where

import           Language.Instance
import           Language.Mapping
import           Language.Parser.Instance
import           Language.Parser.LexerRules
import           Language.Parser.Mapping
import           Language.Parser.Parser
import           Language.Term
import           Language.Transform

-- prelude
import           Data.Maybe

-- megaparsec
import           Text.Megaparsec


gParser :: Parser (String, RawTerm)
gParser = do
  x <- identifier
  _ <- constant "->"
  e <- rawTermParser
  return (x, e)

transformRawParser :: Parser TransExpRaw'
transformRawParser = do
  _ <- constant "literal"
  _ <- constant ":"
  s <- instExpParser
  _ <- constant "->"
  t <- instExpParser
  braces $ p s t
  where
    p s t = do
      i <- optional $ do
        _ <- constant "imports"
        many transExpParser
      e <- optional $ do
        _ <- constant "generators"
        many gParser
      x <- optional $ do
        _ <- constant "options"
        many optionParser
      pure $ TransExpRaw' s t
        (fromMaybe [] e)
        (fromMaybe [] x)
        (fromMaybe [] i)

mapTransParser :: String -> (MappingExp -> TransformExp -> [(String, String)] -> TransformExp) -> Parser TransformExp
mapTransParser s constructor = do
  _ <- constant s
  f <- mapExpParser
  i <- transExpParser
  o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
  return $ constructor f i $ fromMaybe [] o

mapInstTransParser :: String -> (MappingExp -> InstanceExp -> [(String, String)] -> TransformExp) -> Parser TransformExp
mapInstTransParser s constructor = do
  _ <- constant s
  f <- mapExpParser
  i <- instExpParser
  o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
  return $ constructor f i $ fromMaybe [] o

sigmaParser' :: Parser TransformExp
sigmaParser' = mapTransParser "sigma" TransformSigma

sigmaDeltaUnitParser' :: Parser TransformExp
sigmaDeltaUnitParser' = mapInstTransParser "unit" TransformSigmaDeltaUnit

sigmaDeltaCoUnitParser' :: Parser TransformExp
sigmaDeltaCoUnitParser' = mapInstTransParser "counit" TransformSigmaDeltaCoUnit

deltaParser' :: Parser TransformExp
deltaParser' = mapTransParser "delta" TransformDelta

transCompParser :: Parser TransformExp
transCompParser = do
  _ <- constant "["
  f <- transExpParser
  _ <- constant ";"
  g <- transExpParser
  _ <- constant "]"
  return $ TransformComp f g

transExpParser :: Parser TransformExp
transExpParser = transCompParser
  <|> TransformRaw <$> transformRawParser
  <|> TransformVar <$> identifier
  <|> sigmaParser'
  <|> deltaParser'
  <|> sigmaDeltaUnitParser'
  <|> sigmaDeltaCoUnitParser'
  <|> parens transExpParser
  <|> do
    _ <- constant "identity"
    TransformId <$> instExpParser

