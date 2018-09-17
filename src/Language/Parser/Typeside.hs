module Language.Parser.Typeside where

import           Language.Parser.LexerRules
import           Language.Parser.Parser
import           Language.Parser.Types

-- megaparsec
import           Text.Megaparsec

typesideKindParser :: Parser TypesideKind
typesideKindParser = undefined

typesideImportParser :: Parser TypesideImport
typesideImportParser
    = do
        _ <- constant "sql"
        pure TypesideImportSql
    <|> TypesideImportRef <$> identifier

typesideTypeIdParser :: Parser TypesideTypeId
typesideTypeIdParser
    = pure TypesideTypeIdTrue <* constant "true"
    <|> pure TypesideTypeIdFalse <* constant "false"
    <|> TypesideTypeId <$> identifier

typesideFnNameParser :: Parser TypesideFnName
typesideFnNameParser
    = TypesideFnNameBool <$> boolParser
    <|> TypesideFnNameString <$> identifier
