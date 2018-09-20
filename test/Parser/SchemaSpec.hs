{-# LANGUAGE ScopedTypeVariables #-}

module Parser.SchemaSpec where

import           Language.Parser.AQLParser
import           Language.Parser.Generator.Generator
import           Language.Parser.Types

-- hspec
import           Test.Hspec

-- megaparsec
import           Text.Megaparsec

-- QuickCheck
import           Test.QuickCheck

-- semigroups
import           Data.List.NonEmpty                  (fromList, toList)

spec :: Spec
spec = do
  describe "schemaParser" $ do
    specify "parses correctly an Identity schema" $
      forAll identifierGen $ \name ->
        parse schemaExpParser "" ("identity " ++ name) ==
        Right (SchemaExpIdentity name)
    specify "parses correctly an Empty schema" $
      forAll identifierGen $ \name ->
        parse schemaExpParser "" ("empty : " ++ name) ==
        Right (SchemaExpEmpty name)
    it "parses correctly an OfImportAll schema" $
      parse schemaExpParser "" ("schemaOf import_all") ==
      Right SchemaExpOfImportAll
    specify "parses correctly a GetSchemaColimit schema" $
      forAll identifierGen $ \name ->
        parse schemaExpParser "" ("getSchema " ++ name) ==
        Right (SchemaExpGetSchemaColimit name)

  describe "schemaLiteralSectionParser" $ do
    it "parses correctly an empty SchemaLiteralSection" $
      parse schemaLiteralSectionParser "" "" ==
      Right (SchemaLiteralSection [] [] [] [] [] [])
    specify "parses correctly a SchemaLiteralSection with imports" $
      forAll (listOf typesideImportGen) $ \typesideImports ->
        parse
          schemaLiteralSectionParser
          ""
          ("imports " ++ (unwords $ map show typesideImports)) ==
        Right (SchemaLiteralSection typesideImports [] [] [] [] [])
    specify "parses correctly a SchemaLiteralSection with entities" $
      forAll (listOf identifierGen) $ \identifiers ->
        parse
          schemaLiteralSectionParser
          ""
          ("entities " ++ (unwords $ identifiers)) ==
        Right (SchemaLiteralSection [] identifiers [] [] [] [])
    specify "parses correctly a SchemaLiteralSection with foreign keys" $
      withMaxSuccess 30 $
      forAll (listOf schemaForeignSigGen) $ \schemaForeignSigs ->
        parse
          schemaLiteralSectionParser
          ""
          ("foreign_keys " ++ (unwords $ map show schemaForeignSigs)) ==
        Right (SchemaLiteralSection [] [] schemaForeignSigs [] [] [])
    specify "parses correctly a SchemaLiteralSection with path equations" $
      withMaxSuccess 30 $
      forAll (listOf schemaPathEqnSigGen) $ \schemaPathEqnSigs ->
        parse
          schemaLiteralSectionParser
          ""
          ("path_equations " ++ (unwords $ map show schemaPathEqnSigs)) ==
        Right (SchemaLiteralSection [] [] [] schemaPathEqnSigs [] [])
    specify "parses correctly a SchemaLiteralSection with attributes" $
      withMaxSuccess 30 $
      forAll (listOf schemaAttributeSigGen) $ \schemaAttributeSigs ->
        parse
          schemaLiteralSectionParser
          ""
          ("attributes " ++ (unwords $ map show schemaAttributeSigs)) ==
        Right (SchemaLiteralSection [] [] [] [] schemaAttributeSigs [])
    specify "parses correctly a SchemaLiteralSection with every piece" $
      withMaxSuccess 30 $
      forAll
        ((\a b c d e -> (a, b, c, d, e)) <$> listOf typesideImportGen <*>
         listOf identifierGen <*>
         listOf schemaForeignSigGen <*>
         listOf schemaPathEqnSigGen <*>
         listOf schemaAttributeSigGen) $ \(typesideImports, identifiers, schemaForeignSigs, schemaPathEqnSigs, schemaAttributeSigs) ->
        parse
          schemaLiteralSectionParser
          ""
          ("imports " ++
           (unwords $ map show typesideImports) ++
           " entities " ++
           (unwords $ identifiers) ++
           " foreign_keys " ++
           (unwords $ map show schemaForeignSigs) ++
           " path_equations " ++
           (unwords $ map show schemaPathEqnSigs) ++
           " attributes " ++ (unwords $ map show schemaAttributeSigs)) ==
        Right
          (SchemaLiteralSection
             typesideImports
             identifiers
             schemaForeignSigs
             schemaPathEqnSigs
             schemaAttributeSigs
             [])

  describe "schemaForeignSigParser" $ do
    specify "parses correctly a SchemaForeignSig" $
      forAll
        ((\a b c -> (a, b, c)) <$> (fromList <$> listOf1 identifierGen) <*>
         identifierGen <*>
         identifierGen) $ \(schemaForeignIds, originSchemaEntityId, targetSchemaEntityId) ->
        parse
          schemaForeignSigParser
          ""
          ((unwords $ toList schemaForeignIds) ++
           " : " ++ originSchemaEntityId ++ " -> " ++ targetSchemaEntityId) ==
        Right
          (SchemaForeignSig
             schemaForeignIds
             originSchemaEntityId
             targetSchemaEntityId)

  describe "schemaPathEqnSigParser" $ do
    specify "parses correctly a SchemaPathEqnSig" $
      forAll ((\a b -> (a, b)) <$> schemaPathGen <*> schemaPathGen) $ \(schemaPathLeft, schemaPathRight) ->
        parse
          schemaPathEqnSigParser
          ""
          ((show schemaPathLeft) ++ " = " ++ (show schemaPathRight)) ==
        Right (SchemaPathEqnSig schemaPathLeft schemaPathRight)

  describe "schemaPathParser" $ do
    specify "parses correctly a SchemaPathArrowId schemaPath" $
      forAll identifierGen $ \name ->
        parse schemaPathParser "" name == Right (SchemaPathArrowId name)
    specify "parses correctly a SchemaPathDotted schemaPath" $
      forAll ((\a b -> (a, b)) <$> schemaPathGen <*> identifierGen) $ \(schemaPath, name) ->
        parse schemaPathParser "" ((show schemaPath) ++ "." ++ name) ==
        Right (SchemaPathDotted schemaPath name)
    specify "parses correctly a SchemaPathParen schemaPath" $
      forAll ((\a b -> (a, b)) <$> identifierGen <*> schemaPathGen) $ \(name, schemaPath) ->
        parse schemaPathParser "" (name ++ "(" ++ (show schemaPath) ++ ")") ==
        Right (SchemaPathParen name schemaPath)

  describe "schemaAttributeSigParser" $ do
    specify "parses correctly a SchemaAttributeSig" $
      forAll
        ((\a b c -> (a, b, c)) <$> (fromList <$> listOf1 identifierGen) <*>
         identifierGen <*>
         typesideTypeIdGen) $ \(schemaAttributeIds, schemaEntityId, typesideTypeId) ->
        parse
          schemaAttributeSigParser
          ""
          ((unwords $ toList schemaAttributeIds) ++
           " : " ++ schemaEntityId ++ " -> " ++ (show typesideTypeId)) ==
        Right
          (SchemaAttributeSig schemaAttributeIds schemaEntityId typesideTypeId)

  describe "schemaFnParser" $ do
    specify "parses correctly a SchemaFnTypeside" $
      forAll typesideFnNameGen $ \typesideFnName ->
        parse schemaFnParser "" (show typesideFnName) ==
        Right (SchemaFnTypeside typesideFnName)
