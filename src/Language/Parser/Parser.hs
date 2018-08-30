module Language.Parser.Parser where

import Language.Parser.LexerRules
import Language.Parser.ReservedWords

-- megaparsec
import           Text.Megaparsec
import qualified Text.Megaparsec.Char.Lexer as L

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
    where
        p = lowerId <|> upperId <|> specialId
        check x = if x `elem` reservedWords
                    then fail $ "keyword" ++ show x ++ "cannot be used as an identifier"
                    else return x

constant :: String -> Parser String
constant = L.symbol spaceConsumer