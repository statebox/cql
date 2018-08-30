{-# LANGUAGE ScopedTypeVariables #-}

module Parser.SchemaSpec where

import Language.Parser.Generator.Generator
import Language.Parser.Schema
import Language.Parser.ReservedWords

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
                \name -> parse schemaParser "" ("identity " ++ name) == Right (SchemaExpIdentity name)
        specify "parses correctly an Empty schema" $
            forAll identifierGen $
                \name -> parse schemaParser "" ("empty : " ++ name) == Right (SchemaExpEmpty name)
        it "parses correctly an OfImportAll schema" $
            parse schemaParser "" ("schemaOf import_all") == Right SchemaExpOfImportAll