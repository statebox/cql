{-# LANGUAGE ScopedTypeVariables #-}

module Parser.SchemaSpec where

import Language.Parser.Generator.Generator
import Language.Parser.Schema
import Language.Parser.ReservedWords
import Language.Parser.Types

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
        specify "parses correctly a SchemaLiteralSection" $
            forAll