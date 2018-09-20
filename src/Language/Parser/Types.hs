{-# LANGUAGE EmptyDataDeriving #-}

module Language.Parser.Types where

-- scientific
import           Data.Scientific    (Scientific)

-- semigroups
import           Data.List.NonEmpty (NonEmpty, toList)

-- OPTIONS
data AllOptions =
  AllOptions [OptionsDeclaration]
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
data TypesideAssignment = TypesideAssignment TypesideId TypesideExp

type TypesideId = String

data TypesideKind
  = TypesideKindRef TypesideRef
  | TypesideKindExp TypesideExp
  deriving (Eq)

type TypesideRef = String

data TypesideExp
  = TypesideExpEmpty
  | TypesideExpSql
  | TypesideExpOf SchemaKind
  | TypesideExpLiteral (Maybe TypesideLiteralSection)
  deriving (Eq)

data TypesideLiteralSection = TypesideLiteralSection
  [TypesideImport]
  [TypesideTypeSig]
  [TypesideConstantSig]
  [TypesideFunctionSig]
  -- java types
  -- java constants
  -- java functions
  [TypesideEquationSig]
  -- options
  deriving (Eq)

data TypesideImport
  = TypesideImportSql
  | TypesideImportRef TypesideRef
  deriving (Eq)

instance Show TypesideImport where
  show (TypesideImportSql)             = "sql"
  show (TypesideImportRef typesideRef) = typesideRef

type TypesideTypeSig = TypesideTypeId

data TypesideTypeId
  = TypesideTypeIdTrue
  | TypesideTypeIdFalse
  | TypesideTypeId String
  deriving (Eq)

instance Show TypesideTypeId where
  show TypesideTypeIdTrue    = "true"
  show TypesideTypeIdFalse   = "false"
  show (TypesideTypeId name) = name

data TypesideConstantSig = TypesideConstantSig
  (NonEmpty TypesideConstantId)
  TypesideTypeId
  deriving (Eq)

data TypesideConstantId
  = TypesideConstantIdBool Bool
  | TypesideConstantIdString String
  | TypesideConstantIdInteger Integer
  | TypesideConstantIdLowerId String
  | TypesideConstantIdUpperId String
  deriving (Eq)

data TypesideFunctionSig = TypesideFunctionSig
  TypesideFnName
  TypesideFnLocal
  TypesideFnTarget
  deriving (Eq)

data TypesideFnName
  = TypesideFnNameBool Bool
  | TypesideFnNameString String
  deriving (Eq)

instance Show TypesideFnName where
  show (TypesideFnNameBool True)   = "true"
  show (TypesideFnNameBool False)  = "false"
  show (TypesideFnNameString name) = name

type TypesideFnLocal = String

type TypesideFnTarget = String

data TypesideEquationSig
  = TypesideEquationSigForAll (NonEmpty TypesideLocal) TypesideEval TypesideEval
  | TypesideEquationSigEq TypesideEval TypesideEval
  deriving (Eq)

data TypesideLocal = TypesideLocal String (Maybe TypesideLocalType)
  deriving (Eq)

type TypesideLocalType = String

data TypesideEval
  = TypesideEvalNumber Scientific
  | TypesideEvalGen TypesideLiteral
  | TypesideEvalInfix TypesideEval TypesideFnName TypesideEval
  | TypesideEvalParen TypesideFnName [TypesideEval]
  deriving (Eq)

data TypesideLiteral
  = TypesideLiteralLowerId
  | TypesideLiteralUpperId
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
  | SchemaExpLiteral TypesideKind
                     SchemaLiteralSection
  deriving (Eq)

type SchemaColimitRef = String

data SchemaLiteralSection = SchemaLiteralSection
  [TypesideImport]
  [SchemaEntityId]
  [SchemaForeignSig]
  [SchemaPathEqnSig]
  [SchemaAttributeSig]
  [SchemaObservationEquationSig]
  -- options
  deriving (Eq)

type SchemaEntityId = String

data SchemaForeignSig = SchemaForeignSig
  (NonEmpty SchemaForeignId)
  SchemaEntityId
  SchemaEntityId
  deriving (Eq)

instance Show SchemaForeignSig where
  show (SchemaForeignSig foreignIds origin target) =
    (unwords $ toList foreignIds) ++ " : " ++ origin ++ " -> " ++ target

type SchemaForeignId = String

data SchemaPathEqnSig = SchemaPathEqnSig SchemaPath SchemaPath
  deriving (Eq)

instance Show SchemaPathEqnSig where
  show (SchemaPathEqnSig schemaPathLeft schemaPathRight) =
    (show schemaPathLeft) ++ " = " ++ (show schemaPathRight)

data SchemaPath
  = SchemaPathArrowId SchemaArrowId
  | SchemaPathDotted SchemaPath SchemaArrowId
  | SchemaPathParen SchemaArrowId SchemaPath
  deriving (Eq)

instance Show SchemaPath where
  show (SchemaPathArrowId schemaArrowId) = schemaArrowId
  show (SchemaPathDotted schemaPath schemaArrowId) =
    (show schemaPath) ++ "." ++ schemaArrowId
  show (SchemaPathParen schemaArrowId schemaPath) =
    schemaArrowId ++ "(" ++ (show schemaPath) ++ ")"

type SchemaArrowId = String

data SchemaAttributeSig = SchemaAttributeSig
  (NonEmpty SchemaAttributeId)
  SchemaEntityId
  TypesideTypeId
  deriving (Eq)

instance Show SchemaAttributeSig where
  show (SchemaAttributeSig schemaAttributeIds schemaEntityId typesideTypeId)
    = (unwords $ toList schemaAttributeIds)
    ++ " : "
    ++ schemaEntityId
    ++ " -> "
    ++ (show typesideTypeId)

type SchemaAttributeId = String

data SchemaObservationEquationSig
  = SchemaObserveForall SchemaEquationSig
  | SchemaObserveEquation SchemaPath SchemaPath
  deriving (Eq)

data SchemaEquationSig =
  SchemaEquationSig (NonEmpty SchemaGen) EvalSchemaFn EvalSchemaFn
  deriving (Eq)

data SchemaGen =
  SchemaGen String (Maybe SchemaGenType)
  deriving (Eq)

type SchemaGenType = String

data EvalSchemaFn
  = EvalSchemaFnLiteral SchemaLiteralValue
  | EvalSchemaFnGen SchemaGen
  | EvalSchemaFnParen SchemaFn (NonEmpty EvalSchemaFn)
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
