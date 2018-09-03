{-# LANGUAGE EmptyDataDeriving #-} -- TODO: remove

module Language.Parser.Types where

-- scientific
import Data.Scientific (Scientific)

-- OPTIONS

data AllOptions = AllOptions [OptionsDeclaration]
    deriving (Eq)

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
    deriving (Eq)

data CsvOptions
    = CsvFieldDelimChar Char
    | CsvEscapeCharEqual Char
    | CsvQuoteChar Char
    | CsvFileExtension String
    | CsvGenerateIds Bool
    deriving (Eq)

data ProverOptions
    = Prover ProverType
    | ProgramAllowNontermUnsafe Bool
    | CompletionPrecedence [String]
    | CompletionSort Bool
    | CompletionCompose Bool
    | CompletionFilterSubsumed Bool
    | CompletionSyntacticAc Bool
    deriving (Eq)

data ProverType
    = ProverTypeAuto
    | ProverTypeFail
    | ProverTypeFree
    | ProverTypeSaturated
    | ProverTypeCongruence
    | ProverTypeMonoidal
    | ProverTypeProgram
    | ProverTypeCompletion
    deriving (Eq)

data GuiOptions
    = GuiMaxTableSize Integer
    | GuiMaxGraphSize Integer
    | GuiMaxStringSize Integer
    | GuiRowsToDisplay Integer
    deriving (Eq)

data EvalOptions
    = EvalMaxTempSize Integer
    | EvalReorderJoins Bool
    | EvalMaxPlanDepth Integer
    | EvalJoinSelectivity Bool
    | EvalUseIndices Bool
    | EvalApproxSqlUnsafe Bool
    | EvalSqlPersistentIndices Bool
    deriving (Eq)

data CoproductOptions
    = CoproductAllowEntityType Bool
    | CoproductAllowType Bool
    deriving (Eq)

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
    deriving (Eq)

data TypesideTypeId
    = TypesideTypeIdTrue
    | TypesideTypeIdFalse
    | TypesideTypeId String
    deriving (Eq)

data TypesideFnName
    = TypesideFnNameBool Bool
    | TypesideFnNameString String
    deriving (Eq)

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
    | SchemaExpLiteral TypesideKind SchemaLiteralSection
    deriving (Eq)

type SchemaColimitRef = String

data SchemaLiteralSection = SchemaLiteralSection
    [TypesideImport]
    [SchemaEntityId]
    [SchemaForeignSig]
    [SchemaPathEqnSig]
    [SchemaAttributeSig]
    [SchemaObservationEquationSig]
    deriving (Eq)

type SchemaEntityId = String

data SchemaForeignSig = SchemaForeignSig
    SchemaForeignId
    SchemaEntityId
    SchemaEntityId
    deriving (Eq)

type SchemaForeignId = String

data SchemaPathEqnSig = SchemaPathEqnSig SchemaPath SchemaPath
    deriving (Eq)

data SchemaPath
    = SchemaPathArrowId SchemaArrowId
    | SchemaPathDotted SchemaPath SchemaArrowId
    | SchemaPathParen SchemaArrowId SchemaPath
    deriving (Eq)

data SchemaArrowId
    = SchemaArrowIdEntity SchemaEntityId
    | SchemaArrowIdForeign SchemaForeignId
    deriving (Eq)

data SchemaAttributeSig = SchemaAttributeSig [SchemaAttributeId] SchemaEntityId TypesideTypeId
    deriving (Eq)

type SchemaAttributeId = String

data SchemaObservationEquationSig
    = SchemaObserveForall SchemaEquationSig
    | SchemaObserveEquation SchemaPath SchemaPath
    deriving (Eq)

data SchemaEquationSig = SchemaEquationSig SchemaGen [SchemaGen] EvalSchemaFn EvalSchemaFn
    deriving (Eq)

data SchemaGen = SchemaGen String SchemaGenType
    deriving (Eq)

type SchemaGenType = String

data EvalSchemaFn
    = EvalSchemaFnLiteral SchemaLiteralValue
    | EvalSchemaFnGen SchemaGen
    | EvalSchemaFnParen SchemaFn EvalSchemaFn [EvalSchemaFn]
    | EvalSchemaFnDotted EvalSchemaFn SchemaFn
    deriving (Eq)

data SchemaLiteralValue
    = SchemaLiteralValueInt Integer
    | SchemaLiteralValueReal Scientific
    | SchemaLiteralValueBool Bool
    | SchemaLiteralValueText String
    deriving (Eq)

data SchemaFn
    = SchemaFnTypeside TypesideFnName
    | SchemaFnAttr SchemaAttributeId
    | SchemaFnFk SchemaForeignId
    deriving (Eq)
