module Language.Parser.Mapping where

import           Data.Maybe
import           Language.Mapping
import           Language.Parser.LexerRules
import           Language.Parser.Parser
import           Language.Parser.Schema     hiding (attParser, fkParser)
import           Language.Term
import           Text.Megaparsec

--------------------------------------------------------------------------------

fkParser :: Parser (String, [String])
fkParser = do x <- identifier
              _ <- constant "->"
              y <- sepBy1 identifier $ constant "."
              return (x, y)

attParser :: Parser (String, (String, Maybe String, RawTerm))
attParser = do x <- identifier
               _ <- constant "->"
               _ <- constant "lambda"
               y <- identifier
               z <- optional $ do _ <- constant ":"
                                  identifier
               _ <- constant "."
               e <- rawTermParser
               return (x, (y, z, e))

mappingRawParser :: Parser MappingExpRaw'
mappingRawParser = do
        _ <- constant "literal"
        _ <- constant ":"
        s <- schemaExpParser
        _ <- constant "->"
        t <- schemaExpParser
        m <- braces $ (q' s t)
        pure $ m
 where p   = do  x <- do
                    _ <- constant "entity"
                    v <- identifier
                    _ <- constant "->"
                    u <- identifier
                    return (v,u)
                 f <- optional $ do
                    _ <- constant "foreign_keys"
                    many fkParser
                 a <- optional $ do
                    _ <- constant "attributes"
                    many attParser
                 pure $ (x,fromMaybe [] f, fromMaybe [] a)
       q' s t = do i <- optional $ do
                      _ <- constant "imports"
                      many mapExpParser  
                   m <- many p
                   o <- optional $ do
                          _ <- constant "options"
                          many optionParser
                   pure $ q s t (fromMaybe [] o) (fromMaybe [] i) m 

       q s t o i = Prelude.foldr (\(x,fm,am) (MappingExpRaw' s' t' ens' fks' atts' o' i') -> MappingExpRaw' s' t' (x:ens') (fm++fks') (am++atts') o' i') (MappingExpRaw' s t [] [] [] o i)





mapExpParser :: Parser MappingExp
mapExpParser =
    MappingRaw <$> mappingRawParser
    <|>
      MappingVar <$> identifier
    <|>
       do
        _ <- constant "identity"
        x <- schemaExpParser
        return $ MappingId x
    <|> parens mapExpParser
