{-# LANGUAGE EmptyDataDeriving #-} -- TODO: remove

module Language.Parser.Types where

-- scientific
import Data.Scientific (Scientific)

-- OPTIONS

data AllOptions = AllOptions [OptionsDeclaration]

data OptionsDeclaration
    = NumThreadsOption Integer
    | RandomSeedOption Integer
    | TimeoutOption Integer
    | RequireConsistencyOption Bool
    | SchemaOnlyOption Bool
    | AllowJavaEqsUnsafeOption Bool
    | DontValidateUnsafeOption Bool
    | AlwaysReloadOption Bool
    | QueryComposeUseIncomplete Bool
    | CsvOptions CsvOptions
    | IdColumnNameOption String
    | VarcharLengthOption Integer
    | StartIdsAtOption Integer
    | ImportAsTheoryOption Bool
    | JdbcDefaultClassOption String
    | JdbDefaultStringOption String
    | DVIAFProverUnsafeOption Bool
    | ProverOptions ProverOptions
    | GuiOptions GuiOptions
    | EvalOptions EvalOptions
    | QueryRemoveRedundancyOption Bool
    | CoproductOptions CoproductOptions
    | ImportJoinedOption Bool
    | CompletionPresedenceOption String
    | PrependEntityOnIds Bool

data CsvOptions
    = CsvFieldDelimChar Char
    | CsvEscapeCharEqual Char
    | CsvQuoteChar Char
    | CsvFileExtension String
    | CsvGenerateIds Bool

data ProverOptions
    = Prover ProverType
    | ProgramAllowNontermUnsafe Bool
    | CompletionPrecedence [String]
    | CompletionSort Bool
    | CompletionCompose Bool
    | CompletionFilterSubsumed Bool
    | CompletionSyntacticAc Bool

data ProverType
    = ProverTypeAuto
    | ProverTypeFail
    | ProverTypeFree
    | ProverTypeSaturated
    | ProverTypeCongruence
    | ProverTypeMonoidal
    | ProverTypeProgram
    | ProverTypeCompletion

data GuiOptions
    = GuiMaxTableSize Integer
    | GuiMaxGraphSize Integer
    | GuiMaxStringSize Integer
    | GuiRowsToDisplay Integer

data EvalOptions
    = EvalMaxTempSize Integer
    | EvalReorderJoins Bool
    | EvalMaxPlanDepth Integer
    | EvalJoinSelectivity Bool
    | EvalUseIndices Bool
    | EvalApproxSqlUnsafe Bool
    | EvalSqlPersistentIndices Bool

data CoproductOptions
    = CoproductAllowEntityType Bool
    | CoproductAllowType Bool

-- TYPESIDE

data TypesideKind
    = TypesideKindRef TypesideRef
    | TypesideKindExp TypesideExp
    deriving (Eq)

type TypesideRef = String

data TypesideExp
    = TypesideExpEmpty
    | TypesideExpSql
    | TypesideExpOf SchemaKind
    | TypesideExpLiteral TypesideLiteralSection
    deriving (Eq)

data TypesideLiteralSection
    deriving (Eq)

data TypesideImport
    = TypesideImportSql
    | TypesideImportRef TypesideRef

data TypesideTypeId
    = TypesideTypeIdTrue
    | TypesideTypeIdFalse
    | TypesideTypeId String

data TypesideFnName
    = TypesideFnNameBool Bool
    | TypesideFnNameString String

-- SCHEMA

data SchemaKind
    = SchemaKindRef SchemaRef
    | SchemaKindExp SchemaExp
    deriving (Eq)

type SchemaRef = String

data SchemaExp
    = SchemaExpIdentity SchemaRef
    | SchemaExpEmpty TypesideRef
    | SchemaExpOfImportAll
    -- | SchemaExpOfInstance
    | SchemaExpGetSchemaColimit SchemaColimitRef
    | SchemaExpLiteral TypesideKind
    deriving (Eq)

type SchemaColimitRef = String

data SchemaLiteralSection = SchemaLiteralSection
    [TypesideImport]
    [SchemaEntityId]
    [SchemaForeignSig]
    [SchemaPathEqnSig]
    [SchemaAttributeSig]
    [SchemaObservationEquationSig]

type SchemaEntityId = String

data SchemaForeignSig = SchemaForeignSig
    SchemaForeignId
    SchemaEntityId
    SchemaEntityId

type SchemaForeignId = String

data SchemaPathEqnSig = SchemaPathEqnSig
    SchemaPath
    SchemaPath

data SchemaPath
    = SchemaPathArrowId SchemaArrowId
    | SchemaPathDotted SchemaPath SchemaArrowId
    | SchemaPathParen SchemaArrowId SchemaPath

data SchemaArrowId
    = SchemaArrowIdEntity SchemaEntityId
    | SchemaArrowIdForeign SchemaForeignId

data SchemaAttributeSig = SchemaAttributeSig [SchemaAttributeId] SchemaEntityId TypesideTypeId

type SchemaAttributeId = String

data SchemaObservationEquationSig
    = SchemaObserveForall SchemaEquationSig
    | SchemaObserveEquation SchemaPath SchemaPath

data SchemaEquationSig = SchemaEquationSig SchemaGen [SchemaGen] EvalSchemaFn EvalSchemaFn

data SchemaGen = SchemaGen String SchemaGenType

type SchemaGenType = String

data EvalSchemaFn
    = EvalSchemaFnLiteral SchemaLiteralValue
    | EvalSchemaFnGen SchemaGen
    | EvalSchemaFnParen SchemaFn EvalSchemaFn [EvalSchemaFn]
    | EvalSchemaFnDotted EvalSchemaFn SchemaFn

data SchemaLiteralValue
    = SchemaLiteralValueInt Integer
    | SchemaLiteralValueReal Scientific
    | SchemaLiteralValueBool Bool
    | SchemaLiteralValueText String

data SchemaFn
    = SchemaFnTypeside TypesideFnName
    | SchemaFnAttr SchemaAttributeId
    | SchemaFnFk SchemaForeignId
