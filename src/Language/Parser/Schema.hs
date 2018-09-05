module Language.Parser.Schema where

import           Language.Parser.LexerRules
import           Language.Parser.Parser
import           Language.Parser.Types
import           Language.Parser.Typeside

-- base
import           Data.Maybe

-- megaparsec
import           Text.Megaparsec

-- semigroups
import           Data.List.NonEmpty         (fromList)

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
    maybeEntities <- optional $ do
        constant "entities"
        many identifier
    maybeForeignKeys <- optional $ do
        constant "foreign_keys"
        many schemaForeignSigParser
    pure $ SchemaLiteralSection
        (fromMaybe [] maybeImports)
        (fromMaybe [] maybeEntities)
        (fromMaybe [] maybeForeignKeys)
        []
        []
        []

schemaForeignSigParser :: Parser SchemaForeignSig
schemaForeignSigParser = do
    schemaForeignIds <- some identifier
    constant ":"
    originSchemaEntityId <- identifier
    constant "->"
    targetSchemaEntityId <- identifier
    pure $ SchemaForeignSig
        (fromList schemaForeignIds)
        originSchemaEntityId
        targetSchemaEntityId
