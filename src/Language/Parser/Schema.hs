module Language.Parser.Schema where

import           Language.Parser.LexerRules
import           Language.Parser.Parser
import           Language.Parser.Types
import           Language.Parser.Typeside

-- base
import           Data.Maybe

-- megaparsec
import           Text.Megaparsec

schemaExpParser :: Parser SchemaExp
schemaExpParser
    = SchemaExpIdentity <$> do
        constant "identity"
        identifier
    <|> SchemaExpEmpty <$> do
        constant "empty"
        constant ":"
        identifier
    <|> (\s -> SchemaExpOfImportAll) <$> do
        constant "schemaOf"
        constant "import_all"
    <|> SchemaExpGetSchemaColimit <$> do
        constant "getSchema"
        identifier
    <|> do
        constant "literal"
        constant ":"
        typeside <- typesideKindParser
        schemaLiteral <- try (braces schemaLiteralSectionParser)
        pure $ SchemaExpLiteral typeside schemaLiteral

schemaLiteralSectionParser :: Parser SchemaLiteralSection
schemaLiteralSectionParser = do
    maybeImports <- optional $ do
        constant "imports"
        many typesideImportParser
    pure $ SchemaLiteralSection (fromMaybe [] maybeImports) [] [] [] [] []
