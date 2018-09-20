module Language.Parser.Generator.Generator where

import           Language.Parser.ReservedWords
import           Language.Parser.Types

-- QuickCheck
import           Test.QuickCheck.Gen

-- semigroups
import           Data.List.NonEmpty            (fromList)

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

boolGen :: Gen Bool
boolGen = oneof [pure True, pure False]

-- TYPESIDE
typesideImportGen :: Gen TypesideImport
typesideImportGen =
  oneof
    [ pure TypesideImportSql
    , TypesideImportRef <$> (identifierGen `suchThat` (/= "sql"))
    ]

typesideTypeIdGen :: Gen TypesideTypeId
typesideTypeIdGen =
  oneof
    [ pure TypesideTypeIdTrue
    , pure TypesideTypeIdFalse
    , TypesideTypeId <$> identifierGen
    ]

typesideFnNameGen :: Gen TypesideFnName
typesideFnNameGen =
  oneof [TypesideFnNameBool <$> boolGen, TypesideFnNameString <$> identifierGen]

-- SCHEMA
schemaForeignSigGen :: Gen SchemaForeignSig
schemaForeignSigGen =
  SchemaForeignSig
    <$> (fromList <$> listOf1 identifierGen)
    <*> identifierGen
    <*> identifierGen

schemaPathGen :: Gen SchemaPath
schemaPathGen =
  oneof
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
