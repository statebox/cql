module Language.Parser.LexerRules where

-- megaparsec
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- void
import           Data.Void

type Parser = Parsec Void String

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 lineComment blockComment
    where
        lineComment = L.skipLineComment "//"
        blockComment = L.skipBlockComment "(*" "*)"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

idChar :: Parser Char
idChar
    = letterChar
    <|> char '_' 
    <|> char '$'

upperId :: Parser String
upperId = (:) <$> upperChar <*> many (idChar <|> digitChar)

lowerId :: Parser String
lowerId = (:) <$> lowerChar <*> many (idChar <|> digitChar)

specialId :: Parser String
specialId = (:) <$> idChar <*> many (idChar <|> digitChar)