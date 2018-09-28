module Parser.TypesideSpec where

import           Language.Parser.Generator.Generator
import           Language.Parser.Types
import           Language.Parser.Typeside

-- base
import           Data.Char                           (toLower)

-- hspec
import           Test.Hspec

-- megaparsec
import           Text.Megaparsec

-- QuickCheck
import           Test.QuickCheck

spec :: Spec
spec = do
  describe "typesideImportParser" $ do
    it "parses correctly a TypesideImportSql" $
      parse typesideImportParser "" "sql" == Right TypesideImportSql

      {--
    specify "parser correctly a TypesideImportRef" $
      forAll (identifierGen `suchThat` (\s -> not (s == "sql"))) $ \name ->
        parse typesideImportParser "" name == Right (TypesideImportRef name)

  describe "typesideTypeIdParser" $ do
    it "parses correctly a TypesideTypeIdTrue" $
      parse typesideTypeIdParser "" "true" == Right TypesideTypeIdTrue
    it "parses correctly a TypesideTypeIdFalse" $
      parse typesideTypeIdParser "" "false" == Right TypesideTypeIdFalse
    specify "parses correctly a TypesideTypeId" $
      forAll
        (identifierGen `suchThat` (\s -> not (s == "true" || s == "false"))) $ \name ->
        parse typesideTypeIdParser "" name == Right (TypesideTypeId name)

  describe "typesideFnNameParser" $ do
    specify "parses correctly a TypesideFnNameBool" $
      forAll arbitrary $ \bool ->
        parse typesideFnNameParser "" (toLower <$> show bool) ==
        Right (TypesideFnNameBool bool)
    specify "parses correctly a TypesideFnNameString" $
      forAll
        (identifierGen `suchThat` (\s -> not (s == "true" || s == "false"))) $ \name ->
        parse typesideFnNameParser "" name == Right (TypesideFnNameString name)
        --}
