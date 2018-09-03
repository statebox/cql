module Language.Parser.Typeside where

import Language.Parser.LexerRules
import Language.Parser.Parser
import Language.Parser.Types

-- megaparsec
import           Text.Megaparsec

typesideKindParser :: Parser TypesideKind
typesideKindParser = undefined

typesideImportParser :: Parser TypesideImport
typesideImportParser
    = do
        constant "sql"
        pure TypesideImportSql
    <|> TypesideImportRef <$> identifier
