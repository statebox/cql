module Language.Parser.Mapping where

import Language.Mapping
import Text.Megaparsec
import           Data.Maybe

import           Language.Parser.LexerRules
import           Language.Parser.Parser
import Language.Parser.Schema 

--------------------------------------------------------------------------------

fkParsre = do x <- identifier
              _ <- constant "->"
              y <- sepBy1 identifier $ constant "." 
              return (x, y)

attParsre = do x <- identifier
               _ <- constant "->"
               _ <- constant "lambda"
               y <- identifier
             --  _ <- constant ":"
            --   t <- identifier
               _ <- constant "."
               e <- rawTermParser
               return (x, (y, e)) 

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
                    many fkParsre
                 a <- optional $ do
                    _ <- constant "attributes"
                    many attParsre
                 pure $ (x,fromMaybe [] f, fromMaybe [] a)
       q' s t = do m <- many p   
                   o <- optional $ do
                          _ <- constant "options"
                          many optionParser
                   pure $ q s t (fromMaybe [] o) m
     
       q s t o = Prelude.foldr (\(x,fm,am) (MappingExpRaw' s t ens fks atts o) -> MappingExpRaw' s t (x:ens) (fm++fks) (am++atts) o) (MappingExpRaw' s t [] [] [] o)          



                    
     
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