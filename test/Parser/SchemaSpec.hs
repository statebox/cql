{-# LANGUAGE ScopedTypeVariables #-}

module Parser.SchemaSpec where

import           Language.Parser.Generator.Generator
import           Language.Parser.ReservedWords
import           Language.Parser.Schema
import           Language.Parser.Types

-- hspec
import           Test.Hspec

-- megaparsec
import           Text.Megaparsec

-- QuickCheck
import           Test.QuickCheck

spec :: Spec
spec = do
    describe "schemaParser" $ do
        specify "parses correctly an Identity schema" $
            forAll identifierGen $
                \name -> parse schemaExpParser "" ("identity " ++ name) == Right (SchemaExpIdentity name)
        specify "parses correctly an Empty schema" $
            forAll identifierGen $
                \name -> parse schemaExpParser "" ("empty : " ++ name) == Right (SchemaExpEmpty name)
        it "parses correctly an OfImportAll schema" $
            parse schemaExpParser "" ("schemaOf import_all") == Right SchemaExpOfImportAll
        specify "parses correctly a GetSchemaColimit schema" $
            forAll identifierGen $
                \name -> parse schemaExpParser "" ("getSchema " ++ name) == Right (SchemaExpGetSchemaColimit name)
    describe "schemaLiteralSectionParser" $ do
        it "parses correctly an empty SchemaLiteralSection" $
            parse schemaLiteralSectionParser "" "" == Right (SchemaLiteralSection [] [] [] [] [] [])
        specify "parses correctly a SchemaLiteralSection with imports" $
            forAll (listOf typesideImportGen) $
                \typesideImports -> parse schemaLiteralSectionParser "" ("imports " ++ (unwords $ map show typesideImports))
                    == Right (SchemaLiteralSection typesideImports [] [] [] [] [])
        specify "parses correctly a SchemaLiteralSection with entities" $
            forAll (listOf identifierGen) $
                \identifiers -> parse schemaLiteralSectionParser "" ("entities " ++ (unwords $ identifiers))
                    == Right (SchemaLiteralSection [] identifiers [] [] [] [])
        specify "parses correctly a SchemaLiteralSection with every piece" $
            forAll ((\a b -> (a, b)) <$> listOf typesideImportGen <*> listOf identifierGen) $
                \(typesideImports, identifiers) ->
                    parse schemaLiteralSectionParser "" ("imports " ++ (unwords $ map show typesideImports) ++ " entities " ++ (unwords $ identifiers))
                    == Right (SchemaLiteralSection typesideImports identifiers [] [] [] [])
