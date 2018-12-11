{-# LANGUAGE TupleSections #-}

module Language.Parser.Instance where

import           Language.Instance          as I
import           Language.Mapping
import           Language.Parser.LexerRules
import           Language.Parser.Mapping    as M
import           Language.Parser.Parser
import           Language.Parser.Schema
import           Language.Schema            as S
import           Language.Term

-- base
import           Data.Maybe

-- megaparsec
import           Text.Megaparsec

eqParser :: Parser (RawTerm, RawTerm)
eqParser = do
  l <- rawTermParser
  _ <- constant "="
  r <- rawTermParser
  return (l, r)

eqParser2 :: Parser [(RawTerm, RawTerm)]
eqParser2 = do
  r <- many p'
  return $ concat r
  where
    p  = do
      p1 <- rawTermParser
      p2 <- rawTermParser
      return (p1, p2)
    p' = do
      l <- identifier
      _ <- constant "-> {"
      m <- sepBy p $ constant ","
      _ <- constant "}"
      return $ map (\(x, y) -> (RawApp l [x], y)) m

skParser :: Parser [(Gen, En)]
skParser = genParser

genParser :: Parser [(Gen, En)]
genParser = do
  x <- some identifier
  _ <- constant ":"
  y <- identifier
  return $ map (, y) x

mapInstParser :: String -> (MappingExp -> InstanceExp -> [(String, String)] -> InstanceExp) -> Parser InstanceExp
mapInstParser s constructor = do
  _ <- constant s
  f <- mapExpParser
  i <- instExpParser
  o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
  return $ constructor f i $ fromMaybe [] o

sigmaParser :: Parser InstanceExp
sigmaParser = mapInstParser "sigma" InstanceSigma

deltaParser :: Parser InstanceExp
deltaParser = mapInstParser "delta" InstanceDelta

instRawParser :: Parser InstExpRaw'
instRawParser = do
  _ <- constant "literal"
  _ <- constant ":"
  t <- schemaExpParser
  braces $ p t
  where
    p t = do
      i <- optional $ do
        _ <- constant "imports"
        many instExpParser
      e <- optional $ do
        _ <- constant "generators"
        y <- many genParser
        return $ concat y
      o <- optional $ do
        _ <- constant "equations"
        many eqParser
      o2 <- optional $ do
        _ <- constant "multi_equations"
        eqParser2
      x <- optional $ do
        _ <- constant "options"
        many optionParser
      pure $ InstExpRaw' t
        (fromMaybe [] e)
        (fromMaybe [] o ++ fromMaybe [] o2)
        (fromMaybe [] x)
        (fromMaybe [] i)

instExpParser :: Parser InstanceExp
instExpParser
  =   InstanceRaw   <$> instRawParser
  <|> InstanceVar   <$> identifier
  <|> InstancePivot <$> (constant "pivot" *> instExpParser)
  <|> sigmaParser
  <|> deltaParser
  <|> do
    _ <- constant "empty"
    _ <- constant ":"
    InstanceInitial <$> schemaExpParser
  <|> parens instExpParser
