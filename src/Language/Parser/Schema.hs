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

-- semigroups
import           Data.List.NonEmpty         (fromList)

schemaExpParser :: Parser SchemaExp
schemaExpParser
    = SchemaExpIdentity <$> do
        _ <- constant "identity"
        identifier
    <|> SchemaExpEmpty <$> do
        _ <- constant "empty"
        _ <- constant ":"
        identifier
    <|> (\_ -> SchemaExpOfImportAll) <$> do
        _ <- constant "schemaOf"
        constant "import_all"
    <|> SchemaExpGetSchemaColimit <$> do
        _ <- constant "getSchema"
        identifier
    <|> do
        _ <- constant "literal"
        _ <- constant ":"
        typeside <- typesideKindParser
        schemaLiteral <- try (braces schemaLiteralSectionParser)
        pure $ SchemaExpLiteral typeside schemaLiteral

schemaLiteralSectionParser :: Parser SchemaLiteralSection
schemaLiteralSectionParser = do
    maybeImports <- optional $ do
        _ <- constant "imports"
        many typesideImportParser
    maybeEntities <- optional $ do
        _ <- constant "entities"
        many identifier
    maybeForeignKeys <- optional $ do
        _ <- constant "foreign_keys"
        many schemaForeignSigParser
    maybePathEquations <- optional $ do
        _ <- constant "path_equations"
        many schemaPathEqnSigParser
    maybeAttributes <- optional $ do
        _ <- constant "attributes"
        many schemaAttributeSigParser
    maybeObservationEquations <- optional $ do
        _ <- constant "observation_equations"
        many schemaObservationEquationSigParser
    pure $ SchemaLiteralSection
        (fromMaybe [] maybeImports)
        (fromMaybe [] maybeEntities)
        (fromMaybe [] maybeForeignKeys)
        (fromMaybe [] maybePathEquations)
        (fromMaybe [] maybeAttributes)
        (fromMaybe [] maybeObservationEquations)

schemaForeignSigParser :: Parser SchemaForeignSig
schemaForeignSigParser = do
    schemaForeignIds <- some identifier
    _ <- constant ":"
    originSchemaEntityId <- identifier
    _ <- constant "->"
    targetSchemaEntityId <- identifier
    pure $ SchemaForeignSig
        (fromList schemaForeignIds)
        originSchemaEntityId
        targetSchemaEntityId

schemaPathEqnSigParser :: Parser SchemaPathEqnSig
schemaPathEqnSigParser = do
    left <- schemaPathParser
    _ <- constant "="
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
    _ <- constant ":"
    schemaEntityId <- identifier
    _ <- constant "->"
    typesideTypeId <- typesideTypeIdParser
    pure $ SchemaAttributeSig
        (fromList schemaAttributeIds)
        schemaEntityId
        typesideTypeId

schemaObservationEquationSigParser :: Parser SchemaObservationEquationSig -- TODO: write tests
schemaObservationEquationSigParser
    = constant "forall" *> (SchemaObserveForall <$> schemaEquationSigParser)
    <|> do
        schemaPathLeft <- schemaPathParser
        _ <- constant "="
        schemaPathRight <- schemaPathParser
        pure $ SchemaObserveEquation schemaPathLeft schemaPathRight

schemaEquationSigParser :: Parser SchemaEquationSig -- TODO: write tests
schemaEquationSigParser = do
    schemaGens <- sepBy1 schemaGenParser $ constant ","
    _ <- constant "."
    evalSchemaFnLeft <- evalSchemaFnParser
    _ <- constant "="
    evalSchemaFnRight <- evalSchemaFnParser
    pure $ SchemaEquationSig (fromList schemaGens) evalSchemaFnLeft evalSchemaFnRight

schemaGenParser :: Parser SchemaGen -- TODO: write tests
schemaGenParser = do
    name <- identifier
    maybeSchemaGenType <- optional $ do
        _ <- constant ":"
        identifier
    pure $ SchemaGen name maybeSchemaGenType

evalSchemaFnParser :: Parser EvalSchemaFn -- TODO: write tests
evalSchemaFnParser
    = do
        prefix <- EvalSchemaFnLiteral <$> schemaLiteralValueParser
        suffixes <- many $ constant "." *> schemaFnParser
        pure $ foldl' EvalSchemaFnDotted prefix suffixes
    <|> do
        prefix <- EvalSchemaFnGen <$> schemaGenParser
        suffixes <- many $ constant "." *> schemaFnParser
        pure $ foldl' EvalSchemaFnDotted prefix suffixes
    <|> do
        prefix <- do
            schemaFn <- schemaFnParser
            _ <- constant "("
            evalSchemaFns <- sepBy1 evalSchemaFnParser $ constant ","
            _ <- constant ")"
            pure $ EvalSchemaFnParen schemaFn (fromList evalSchemaFns)
        suffixes <- many $ constant "." *> schemaFnParser
        pure $ foldl' EvalSchemaFnDotted prefix suffixes

schemaLiteralValueParser :: Parser SchemaLiteralValue -- TODO: write tests
schemaLiteralValueParser
    = SchemaLiteralValueInt <$> integerParser
    <|> SchemaLiteralValueReal <$> scientificParser
    <|> SchemaLiteralValueBool <$> boolParser
    <|> SchemaLiteralValueText <$> textParser

schemaFnParser :: Parser SchemaFn
schemaFnParser
    = SchemaFnTypeside <$> typesideFnNameParser
    <|> SchemaFnAttr <$> identifier
    <|> SchemaFnFk <$> identifier
