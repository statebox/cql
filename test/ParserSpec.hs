module ParserSpec where

import           Language.Parser

-- hspec
import           Test.Hspec

-- megaparsec
import           Text.Megaparsec

spec :: Spec
spec = do
    it "parses correctly a schema" $
        parse
            schemaParser
            ""
            "Schema S = literal : Ty { \
            \    entities \
            \        Person \
            \        Company \
            \        CompanyPerson \
            \    foreign_keys \
            \        persons_id   : CompanyPerson -> Person \
            \        companies_id : CompanyPerson -> Company \
            \    attributes \
            \        firstname lastname : Person  -> String \
            \        name      : Company -> String \
            \}"
            == Right (
                SchemaStmt
                    "S"
                    "Ty"
                    ( SchemaDef
                        [ EntityDef "Person"
                        , EntityDef "Company"
                        , EntityDef "CompanyPerson"
                        ]
                        [ ForeignKeyDef "persons_id" "CompanyPerson" "Person"
                        , ForeignKeyDef "companies_id" "CompanyPerson" "Company"
                        ]
                        [ AttributeDef ["firstname", "lastname"] "Person" "String"
                        , AttributeDef ["name"] "Company" "String"]
                    )
                )
