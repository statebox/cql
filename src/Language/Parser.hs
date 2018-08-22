module Language.Parser where

import           Language.AQL

-- base
import           Control.Monad              (void)

-- megaparsec
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- void
import           Data.Void

data Statement
    = SchemaStmt String String SchemaDef
    deriving (Eq)

data SchemaDef = SchemaDef [EntityDef] [ForeignKeyDef] [AttributeDef]
    deriving (Eq)

data EntityDef = EntityDef String
    deriving (Eq)

data ForeignKeyDef = ForeignKeyDef String String String -- name entity referenced_entity
    deriving (Eq)

data AttributeDef = AttributeDef [String] String String -- name entity type
    deriving (Eq)

type Parser = Parsec Void String

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 lineComment blockComment
    where
        lineComment = L.skipLineComment "//"
        blockComment = L.skipBlockComment "(*" "*)"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: String -> Parser String
symbol = L.symbol spaceConsumer

reservedWords :: [String]
reservedWords =
    [ "sigma_chase"
    , "entity"
    , "md"
    , "quotient_jdbc"
    , "random"
    , "sql"
    , "chase"
    , "check"
    , "import_csv"
    , "quotient_csv"
    , "coproduct"
    , "simple"
    , "assert_consistent"
    , "coproduct_sigma"
    , "coequalize"
    , "html"
    , "quotient"
    , "entity_equations"
    , "schema_colimit"
    , "exists"
    , "constraints"
    , "getMapping"
    , "getSchema"
    , "typeside"
    , "schema"
    , "mapping"
    , "instance"
    , "transform"
    , "query"
    , "command"
    , "graph"
    , "exec_jdbc"
    , "exec_js"
    , "exec_cmdline"
    , "literal"
    , "add_to_classpath"
    , "identity"
    , "match"
    , "attributes"
    , "empty"
    , "imports"
    , "types"
    , "constants"
    , "functions"
    , "equations"
    , "forall"
    , "java_types"
    , "multi_equations"
    , "pi"
    , "bindings"
    , "toQuery"
    , "toCoQuery"
    , "anonymize"
    , "frozen"
    , "params"
    , "java_constants"
    , "java_functions"
    , "options"
    , "entities"
    , "src"
    , "unique"
    , "dst"
    , "path_equations"
    , "observation_equations"
    , "generators"
    , "rename"
    , "remove"
    , "modify"
    , "foreign_keys"
    , "lambda"
    , "sigma"
    , "delta"
    , "pi"
    , "unit"
    , "counit"
    , "eval"
    , "coeval"
    , "ed"
    , "chase"
    , "from"
    , "where"
    , "return"
    , "pivot"
    , "copivot"
    , "colimit"
    , "nodes"
    , "edges"
    , "typesideOf"
    , "schemaOf"
    , "distinct"
    , "import_csv"
    , "export_csv_instance"
    , "export_csv_transform"
    , "import_jdbc"
    , "import_jdbc_all"
    , "export_jdbc_transform"
    , "export_jdbc_instance"
    , "export_jdbc_query"
    , "unit_query"
    , "counit_query"
    , "union"
    , "wrap"
    ]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
    where
        p = (:) <$> letterChar <*> many (alphaNumChar <|> char '_')
        check x = if x `elem` reservedWords
                    then fail $ "keyword" ++ show x ++ "cannot be used as an identifier"
                    else return x

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

schemaParser :: Parser Statement
schemaParser = do
    void (symbol "Schema")
    name <- identifier
    void (symbol "=")
    void (symbol "literal") -- can it be something else?
    void (symbol ":")
    typeSide <- identifier
    schemaDef <- braces schemaContentParser
    return (SchemaStmt name typeSide schemaDef)

schemaContentParser :: Parser SchemaDef
schemaContentParser = do
    void (symbol "entities")
    entities <- someTill entityParser (lookAhead $ symbol "foreign_keys")
    void (symbol "foreign_keys")
    foreignKeys <- someTill foreignKeyParser (lookAhead $ symbol "attributes")
    void (symbol "attributes")
    attributes <- some attributeParser
    return (SchemaDef entities foreignKeys attributes)

entityParser :: Parser EntityDef
entityParser = do
    entity <- identifier
    return (EntityDef entity)

foreignKeyParser :: Parser ForeignKeyDef
foreignKeyParser = do
    foreignKey <- identifier
    void (symbol ":")
    entity <- identifier
    void (symbol "->")
    referencedEntity <- identifier
    return (ForeignKeyDef foreignKey entity referencedEntity)

attributeParser :: Parser AttributeDef
attributeParser = do
    attributes <- someTill identifier (lookAhead $ symbol ":")
    void (symbol ":")
    entity <- identifier
    void (symbol "->")
    type' <- identifier
    return (AttributeDef attributes entity type')
