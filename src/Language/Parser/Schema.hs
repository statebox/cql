module Language.Parser.Schema where

import Language.Parser.LexerRules
import Language.Parser.Parser
import Language.Parser.Typeside

-- base
import Control.Applicative ((<|>))

type SchemaRef = String

data SchemaExp
    = SchemaExpIdentity SchemaRef
    | SchemaExpEmpty TypesideRef
    | SchemaExpOfImportAll
    deriving (Eq)

schemaParser :: Parser SchemaExp
schemaParser
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