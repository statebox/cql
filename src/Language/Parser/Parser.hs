module Language.Parser.Parser where

import           Language.Parser.LexerRules
import           Language.Parser.ReservedWords

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
        check x = if x `elem` reservedWords
                    then fail $ "keyword" ++ show x ++ "cannot be used as an identifier"
                    else return x

constant :: String -> Parser String
constant = L.symbol spaceConsumer

braces :: Parser a -> Parser a
braces = between (constant "{") (constant "}")

integerParser :: Parser Integer -- TODO: write tests
integerParser = lexeme L.decimal

scientificParser :: Parser Scientific -- TODO: write tests
scientificParser = lexeme L.scientific

boolParser :: Parser Bool -- TODO: write tests
boolParser
    = pure True <* constant "true"
    <|> pure False <* constant "false"

textParser :: Parser String -- TODO: write tests
textParser = do
    _ <- constant "\""
    text <- many (escapeSeq <|> show <$> noneOf ['"', '\r', '\n', '\\']) -- TODO: check if the escping is correct
    _ <- constant "\""
    pure $ unwords text

escapeSeq :: Parser String -- TODO: write tests
escapeSeq = do
    _ <- char '\\'
    escaped <- show <$> oneOf ['b', 't', 'n', 'f', 'r', '"', '\'', '\\', '.']
        <|> unicodeEsc
        <|> eof *> pure ""
    pure escaped

unicodeEsc :: Parser String -- TODO: write tests
unicodeEsc
    = char 'u' *> pure "u"
    <|> (:) <$> (char 'u') <*> (show <$> hexDigitChar)
    <|> (:) <$> (char 'u') <*> ((:) <$> hexDigitChar <*> (show <$> hexDigitChar))
    <|> (:) <$> (char 'u') <*> ((:) <$> hexDigitChar <*> ((:) <$> hexDigitChar <*> (show <$> hexDigitChar)))
