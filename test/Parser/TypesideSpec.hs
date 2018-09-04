module Parser.TypesideSpec where

import           Language.Parser.Generator.Generator
import           Language.Parser.Types
import           Language.Parser.Typeside

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
        specify "parser correctly a TypesideImportRef" $
            forAll (identifierGen `suchThat` (\s -> not (s == "sql"))) $
                \name -> parse typesideImportParser "" name == Right (TypesideImportRef name)
