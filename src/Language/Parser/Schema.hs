module Language.Parser.Schema where

import Language.Parser.LexerRules
import Language.Parser.Parser
import Language.Parser.Types
import Language.Parser.Typeside

-- base
import Control.Applicative ((<|>))

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
    <|> SchemaExpLiteral <$> do
        constant "literal"
        constant ":"
        typesideKindParser
