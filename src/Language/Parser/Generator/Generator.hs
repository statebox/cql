module Language.Parser.Generator.Generator where

import           Language.Parser.ReservedWords
import           Language.Parser.Types

-- QuickCheck
import           Test.QuickCheck.Arbitrary     (arbitrary)
import           Test.QuickCheck.Gen

-- semigroups
import           Data.List.NonEmpty            (fromList)

-- scientific
import           Data.Scientific               (Scientific, scientific)


-- BASIC
lowerCharGen :: Gen Char
lowerCharGen = elements ['a' .. 'z']

upperCharGen :: Gen Char
upperCharGen = elements ['A' .. 'Z']

idCharGen :: Gen Char
idCharGen = oneof [lowerCharGen, upperCharGen, elements ['_', '$']]

digitCharGen :: Gen Char
digitCharGen = elements ['0' .. '9']

upperIdGen :: Gen String
upperIdGen =
  ((:) <$> upperCharGen <*>
    listOf (oneof [idCharGen, digitCharGen])) `suchThat`
      (\s -> not (s `elem` reservedWords))

lowerIdGen :: Gen String
lowerIdGen =
  ((:) <$> lowerCharGen <*>
    listOf (oneof [idCharGen, digitCharGen])) `suchThat`
      (\s -> not (s `elem` reservedWords))

specialIdGen :: Gen String
specialIdGen = (:) <$> idCharGen <*> listOf (oneof [idCharGen, digitCharGen])

identifierGen :: Gen String
identifierGen = (oneof [lowerIdGen, upperIdGen, specialIdGen])

scientificGen :: Gen Scientific
scientificGen = scientific <$> arbitrary <*> arbitrary

-- textGen :: Gen String
-- textGen = unwords <$> (listOf $ oneof
--   [ escapeSeqGen
--   , arbitrary `suchThat` (\s -> not (s `elem` (show <$> ['"', '\r', '\n', '\\'])))
--   ])

escapeSeqGen :: Gen String
escapeSeqGen = (:) <$> pure '\\' <*> oneof
  [ (: []) <$> oneof
    [ pure 'b'
    , pure 't'
    , pure 'n'
    , pure 'f'
    , pure 'r'
    , pure '\''
    , pure '\\'
    , pure '\0'
    , pure '\a'
    , pure '\v'
    , pure '.'
    ]
  , unicodeEscGen
  ]

unicodeEscGen :: Gen String
unicodeEscGen
  = oneof
    [ pure "u"
    , (\a b c -> a : b : c) <$> pure 'u' <*> hexDigitGen <*> pure []
    , (\a b c d -> a : b : c : d) <$> pure 'u' <*> hexDigitGen <*> hexDigitGen <*> pure []
    , (\a b c d e -> a : b : c : d : e) <$> pure 'u' <*> hexDigitGen <*> hexDigitGen <*> hexDigitGen <*> pure []
    ]

hexDigitGen :: Gen Char
hexDigitGen = oneof
  [ elements ['a' .. 'f']
  , elements ['A' .. 'F']
  , elements ['0' .. '9']
  ]

-- TYPESIDE
typesideImportGen :: Gen TypesideImport
typesideImportGen = oneof
  [ pure TypesideImportSql
  , TypesideImportRef <$> (identifierGen `suchThat` (/= "sql"))
  ]

typesideTypeIdGen :: Gen TypesideTypeId
typesideTypeIdGen = oneof
  [ pure TypesideTypeIdTrue
  , pure TypesideTypeIdFalse
  , TypesideTypeId <$> identifierGen
  ]

typesideConstantSigGen :: Gen TypesideConstantSig
typesideConstantSigGen = TypesideConstantSig
  <$> (fromList <$> listOf1 typesideConstantIdGen)
  <*> typesideTypeIdGen

typesideConstantIdGen :: Gen TypesideConstantId
typesideConstantIdGen = oneof
  [ TypesideConstantIdBool <$> arbitrary
  , TypesideConstantIdInteger <$> arbitrary
  , TypesideConstantIdLowerId <$> lowerIdGen
  , TypesideConstantIdUpperId <$> upperIdGen
  ]

typesideFunctionSigGen :: Gen TypesideFunctionSig
typesideFunctionSigGen = TypesideFunctionSig
  <$> typesideFnNameGen
  <*> (fromList <$> listOf1 identifierGen)
  <*> identifierGen

typesideFnNameGen :: Gen TypesideFnName
typesideFnNameGen = oneof
  [ TypesideFnNameBool <$> arbitrary
  , TypesideFnNameString <$> identifierGen
  ]

typesideEquationSigGen :: Gen TypesideEquationSig
typesideEquationSigGen = oneof
  [ TypesideEquationSigForAll
    <$> (fromList <$> listOf1 typesideLocalGen)
    <*> typesideEvalGen
    <*> typesideEvalGen
  , TypesideEquationSigEq
    <$> typesideEvalGen
    <*> typesideEvalGen
  ]

typesideLocalGen :: Gen TypesideLocal
typesideLocalGen = TypesideLocal
  <$> identifierGen
  <*> (Just <$> identifierGen)

typesideEvalGen :: Gen TypesideEval
typesideEvalGen = oneof
  [ TypesideEvalNumber <$> scientificGen
  , TypesideEvalGen <$> typesideLiteralGen
  , TypesideEvalInfix <$> typesideEvalGen <*> typesideFnNameGen <*> typesideEvalGen
  , TypesideEvalParen <$> typesideFnNameGen <*> (fromList <$> listOf1 typesideEvalGen)
  ]

typesideLiteralGen :: Gen TypesideLiteral
typesideLiteralGen = oneof
  [ TypesideLiteralLowerId <$> lowerIdGen
  , TypesideLiteralUpperId <$> upperIdGen
  ]

-- SCHEMA
schemaForeignSigGen :: Gen SchemaForeignSig
schemaForeignSigGen =
  SchemaForeignSig
    <$> (fromList <$> listOf1 identifierGen)
    <*> identifierGen
    <*> identifierGen

schemaPathGen :: Gen SchemaPath
schemaPathGen = oneof
  [ SchemaPathArrowId <$> identifierGen
  , SchemaPathDotted <$> schemaPathGen <*> identifierGen
  , SchemaPathParen <$> identifierGen <*> schemaPathGen
  ]

schemaPathEqnSigGen :: Gen SchemaPathEqnSig
schemaPathEqnSigGen = SchemaPathEqnSig <$> schemaPathGen <*> schemaPathGen

schemaAttributeSigGen :: Gen SchemaAttributeSig
schemaAttributeSigGen =
  SchemaAttributeSig
    <$> (fromList <$> listOf1 identifierGen)
    <*> identifierGen
    <*> typesideTypeIdGen
