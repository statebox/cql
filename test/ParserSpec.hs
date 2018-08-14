module ParserSpec where

import           Language.Parser

-- hspec
import           Test.Hspec

-- megaparsec
import           Text.Megaparsec

spec :: Spec
spec = do
    it "parses correctly a schema" $
        parse statement "" "Schema" == Right "Schema"
