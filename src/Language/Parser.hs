module Language.Parser where

import           Language.AQL

-- megaparsec
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- void
import           Data.Void

data Statement var ty sym en fk att
    = SchemaDef String (Schema var ty sym en fk att)

type Parser = Parsec Void String

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 lineComment blockComment
    where
        lineComment = L.skipLineComment "//"
        blockComment = L.skipBlockComment "(*" "*)"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: String -> Parser String
symbol = L.symbol spaceConsumer

statement :: Parser String
statement = symbol "Schema"
