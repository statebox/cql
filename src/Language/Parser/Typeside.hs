module Language.Parser.Typeside where

import           Language.Parser.LexerRules
import           Language.Parser.Parser
import           Language.Parser.Types as T

-- megaparsec
import           Text.Megaparsec
import Language.Typeside as X


convTypesideExp :: T.TypesideExp -> X.TypesideExp
convTypesideExp T.TypesideExpEmpty = X.TypesideInitial
convTypesideExp T.TypesideExpSql= undefined
convTypesideExp (T.TypesideExpOf s)= undefined
convTypesideExp (T.TypesideExpLiteral x)= undefined
convTypesideExp (T.TypesideVar v)= X.TypesideVar v

typesideExpParser :: Parser X.TypesideExp
typesideExpParser = do x <- typesideExpParser'
                       return $ convTypesideExp x


typesideExpParser' :: Parser T.TypesideExp
typesideExpParser' = do _ <- constant "empty" -- for now
                        return TypesideExpEmpty 
                 <|> do x <- identifier
                        return $ T.TypesideVar x   

typesideImportParser :: Parser TypesideImport
typesideImportParser
    = do
        _ <- constant "sql"
        pure TypesideImportSql
    <|> TypesideImportRef <$> identifier

typesideTypeIdParser :: Parser TypesideTypeId
typesideTypeIdParser
    = -- pure TypesideTypeIdTrue <* constant "true"
    -- <|> pure TypesideTypeIdFalse <* constant "false"
    -- <|> 
    TypesideTypeId <$> identifier

typesideFnNameParser :: Parser TypesideFnName
typesideFnNameParser
    = --TypesideFnNameBool <$> boolParser
    -- <|> 
    TypesideFnNameString <$> identifier
