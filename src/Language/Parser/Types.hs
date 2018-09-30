{-# LANGUAGE EmptyDataDeriving #-}

module Language.Parser.Types where

-- scientific
import           Data.Scientific    (Scientific)

-- semigroups
import           Data.List.NonEmpty (NonEmpty, toList)

import Language.Term (RawTerm)
import Language.Typeside 


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
