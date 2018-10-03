module Language.Parser.AQLParser where

import           Language.Parser.LexerRules
import           Language.Parser.Parser
import           Language.Parser.Types

-- base
import           Data.List                  (foldl')
import           Data.Maybe

-- megaparsec
import           Text.Megaparsec

-- semigroups
import           Data.List.NonEmpty         (fromList)

-- TYPESIDE
typesideAssignmentParser :: Parser TypesideAssignment -- TODO: write tests
typesideAssignmentParser = do
  _ <- constant "typeside"
  typesideId <- identifier
  _ <- constant "="
  typesideExp <- typesideExpParser
  pure $ TypesideAssignment typesideId typesideExp

typesideExpParser :: Parser TypesideExp -- TODO: write tests
typesideExpParser
  = pure TypesideExpEmpty <* constant "empty"
  <|> pure TypesideExpSql <* constant "sql"
  <|> TypesideExpOf <$> schemaKindParser
  <|> do
    _ <- constant "literal"
    TypesideExpLiteral <$> (optional $ braces typesideLiteralSectionParser)

typesideKindParser :: Parser TypesideKind -- TODO: write tests
typesideKindParser
  = TypesideKindRef <$> identifier
  <|> TypesideKindExp <$> typesideExpParser
  <|> TypesideKindExp <$> (constant "(" *> typesideExpParser <* constant ")")

typesideLiteralSectionParser :: Parser TypesideLiteralSection
typesideLiteralSectionParser = do
  maybeImports <- optional $ do
    _ <- constant "imports"
    many typesideImportParser
  maybeTypes <- optional $ do
    _ <- constant "types"
    many typesideTypeIdParser
  maybeConstants <- optional $ do
    _ <- constant "constants"
    manyTill typesideConstantSigParser (lookAhead $ constant "functions" *> pure () <|> constant "equations" *> pure () <|> eof) -- TODO: check if this works with a subsequent parser
  maybeFunctions <- optional $ do
    _ <- constant "functions"
    many typesideFunctionSigParser
  maybeEquations <- optional $ do
    _ <- constant "equations"
    many typesideEquationSigParser
  pure $ TypesideLiteralSection
    (fromMaybe [] maybeImports)
    (fromMaybe [] maybeTypes)
    (fromMaybe [] maybeConstants)
    (fromMaybe [] maybeFunctions)
    (fromMaybe [] maybeEquations)

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

typesideConstantSigParser :: Parser TypesideConstantSig
typesideConstantSigParser = do
  typesideConstantIds <- some typesideConstantIdParser
  _ <- constant ":"
  typesideTypeId <- typesideTypeIdParser
  pure $ TypesideConstantSig (fromList typesideConstantIds) typesideTypeId

typesideConstantIdParser :: Parser TypesideConstantId
typesideConstantIdParser
  = TypesideConstantIdBool <$> boolParser
  -- <|> TypesideConstantIdText <$> textParser
  <|> TypesideConstantIdInteger <$> integerParser
  <|> TypesideConstantIdLowerId <$> lexeme lowerId
  <|> TypesideConstantIdUpperId <$> lexeme upperId

typesideFunctionSigParser :: Parser TypesideFunctionSig
typesideFunctionSigParser = do
  typesideFnName <- typesideFnNameParser
  _ <- constant ":"
  typesideFnLocals <- sepBy1 identifier (constant ",")
  _ <- constant "->"
  typesideFnTarget <- identifier
  pure $ TypesideFunctionSig
    typesideFnName
    (fromList typesideFnLocals)
    typesideFnTarget

typesideEquationSigParser :: Parser TypesideEquationSig
typesideEquationSigParser
  = do
    _ <- constant "forall"
    typesideLocals <- sepBy1 typesideLocalParser (constant "," <|> constant " ")
    _ <- constant "."
    typesideEvalLeft <- typesideEvalParser
    _ <- constant "="
    typesideEvalRight <- typesideEvalParser
    pure $ TypesideEquationSigForAll
      (fromList typesideLocals)
      typesideEvalLeft
      typesideEvalRight
  <|> do
    typesideEvalLeft <- typesideEvalParser
    _ <- constant "="
    typesideEvalRight <- typesideEvalParser
    pure $ TypesideEquationSigEq
      typesideEvalLeft
      typesideEvalRight

typesideLocalParser :: Parser TypesideLocal
typesideLocalParser = TypesideLocal
  <$> identifier
  <*> (optional $ constant ":" *> identifier)

typesideEvalParser :: Parser TypesideEval
typesideEvalParser
  = TypesideEvalNumber <$> scientificParser
  <|> do
    _ <- constant "("
    typesideEvalLeft <- typesideEvalParser
    typesideFnName <- typesideFnNameParser
    typesideEvalRight <- typesideEvalParser
    _ <- constant ")"
    pure $ TypesideEvalInfix
      typesideEvalLeft
      typesideFnName
      typesideEvalRight
  <|> try (do
    typesideFnName <- typesideFnNameParser
    _ <- constant "("
    typesideEvals <- sepBy1 typesideEvalParser (constant ",")
    _ <- constant ")"
    pure $ TypesideEvalParen typesideFnName (fromList typesideEvals))
  <|> TypesideEvalGen <$> typesideLiteralParser

typesideLiteralParser :: Parser TypesideLiteral
typesideLiteralParser
  = TypesideLiteralLowerId <$> lexeme lowerId
  <|> TypesideLiteralUpperId <$> lexeme upperId


-- SCHEMA
schemaKindParser :: Parser SchemaKind -- TODO: write tests
schemaKindParser
  = SchemaKindRef <$> identifier
  <|> SchemaKindExp <$> schemaExpParser
  <|> constant "(" *> (SchemaKindExp <$> schemaExpParser) <* constant ")"

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
    typesideKind <- typesideKindParser
    schemaLiteral <- try (braces schemaLiteralSectionParser)
    pure $ SchemaExpLiteral typesideKind schemaLiteral

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
schemaPathParser = do
  prefix <- identifier
  maybeParen <- optional $ constant "(" *> schemaPathParser <* constant ")"
  suffixes <- many $ constant "." *> identifier
  let prefixWithParens =
        case maybeParen of
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
  pure $
    SchemaEquationSig (fromList schemaGens) evalSchemaFnLeft evalSchemaFnRight

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
