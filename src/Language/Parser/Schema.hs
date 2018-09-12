module Language.Parser.Schema where

import           Language.Parser.LexerRules
import           Language.Parser.Parser
import           Language.Parser.Types
import           Language.Parser.Typeside

-- base
import           Data.List                  (foldl')
import           Data.Maybe

-- megaparsec
import           Text.Megaparsec
import           Text.Megaparsec.Expr

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
    maybePathEquations <- optional $ do
        constant "path_equations"
        many schemaPathEqnSigParser
    maybeAttributes <- optional $ do
        constant "attributes"
        many schemaAttributeSigParser
    pure $ SchemaLiteralSection
        (fromMaybe [] maybeImports)
        (fromMaybe [] maybeEntities)
        (fromMaybe [] maybeForeignKeys)
        (fromMaybe [] maybePathEquations)
        (fromMaybe [] maybeAttributes)
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

schemaPathEqnSigParser :: Parser SchemaPathEqnSig
schemaPathEqnSigParser = do
    left <- schemaPathParser
    constant "="
    right <- schemaPathParser
    pure $ SchemaPathEqnSig left right

schemaPathParser :: Parser SchemaPath
schemaPathParser
    = do
        prefix <- identifier
        maybeParen <- optional $ constant "(" *> schemaPathParser <* constant ")"
        suffixes <- many $ constant "." *> identifier
        let
            prefixWithParens = case maybeParen of
                Just paren -> SchemaPathParen prefix paren
                Nothing    -> SchemaPathArrowId prefix
        pure $ foldl' SchemaPathDotted prefixWithParens suffixes

schemaAttributeSigParser :: Parser SchemaAttributeSig
schemaAttributeSigParser = do
    schemaAttributeIds <- some identifier
    constant ":"
    schemaEntityId <- identifier
    constant "->"
    typesideTypeId <- typesideTypeIdParser
    pure $ SchemaAttributeSig
        (fromList schemaAttributeIds)
        schemaEntityId
        typesideTypeId
