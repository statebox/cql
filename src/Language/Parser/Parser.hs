module Language.Parser.Parser where

import           Language.Parser.LexerRules
import           Language.Parser.ReservedWords

-- base
import           Data.Foldable                 (fold)

-- megaparsec
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

-- scientific
import           Data.Scientific               (Scientific)

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p = lowerId <|> upperId <|> specialId
    check x =
      if x `elem` reservedWords
        then fail $ "keyword" ++ show x ++ "cannot be used as an identifier"
        else return x

constant :: String -> Parser String
constant = L.symbol spaceConsumer

braces :: Parser a -> Parser a
braces = between (constant "{") (constant "}")

integerParser :: Parser Integer
integerParser = L.signed spaceConsumer (lexeme L.decimal)

scientificParser :: Parser Scientific
scientificParser = L.signed spaceConsumer (lexeme L.scientific)

boolParser :: Parser Bool
boolParser
  = pure True <* constant "true"
  <|> pure False <* constant "false"

textParser :: Parser String -- TODO: write tests
textParser = do
  _ <- char '"'
  text <- many (escapeSeq <|> (: []) <$> noneOf ['"', '\r', '\n', '\\']) -- TODO: check if the escaping is correct
  _ <- char '"'
  pure $ fold text

escapeSeq :: Parser String
escapeSeq
  = try ((:) <$> char '\\' <*> unicodeEsc)
  <|> try ((:) <$> char '\\' <*> (eof *> pure ""))
  <|> (: []) <$> oneOf ['\b', '\t', '\n', '\f', '\r', '\'', '\\', '\0', '\a', '\v']
  -- <|> pure "\\."

unicodeEsc :: Parser String
unicodeEsc
  = try ((\a b c d e -> a : b : c : d : e)
    <$> (char 'u')
    <*> hexDigitChar
    <*> hexDigitChar
    <*> hexDigitChar
    <*> pure [])
  <|> try ((\a b c d -> a : b : c : d)
    <$> (char 'u')
    <*> hexDigitChar
    <*> hexDigitChar
    <*> pure [])
  <|> try ((\a b c -> a : b : c)
    <$> (char 'u')
    <*> hexDigitChar
    <*> pure [])
  <|> char 'u' *> pure "u"
