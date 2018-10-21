module Language.Parser.Schema where

import           Language.Parser.LexerRules
import           Language.Parser.Parser

-- base
import           Data.Maybe

-- megaparsec
import           Text.Megaparsec

import           Language.Parser.Typeside
import           Language.Schema            as X
import           Language.Term
import           Language.Typeside 

obsEqParser :: Parser (String, String, RawTerm, RawTerm)
obsEqParser = do _ <- constant "forall"
                 i <- identifier
                 j <- optional $ do { _ <- constant ":"; identifier }
                 _ <- constant "."
                 l <- rawTermParser
                 _ <- constant "="
                 r <- rawTermParser
                 case j of
                    Nothing -> error $ "Type inference not supported for now"
                    Just s' -> return (i,s',l,r)

attParser :: Parser [(Att, (En, Ty))]
attParser = fkParser


fkParser :: Parser [(Fk, (En, En))]
fkParser = do x <- some identifier
              _ <- constant ":"
              y <- identifier
              _ <- constant "->"
              z <- identifier
              return $ map (\a -> (a,(y,z))) x

pathEqParser :: Parser ([Fk],[Fk])
pathEqParser = do x <- sepBy1 identifier $ constant "."
                  _ <- constant "="
                  y <- sepBy1 identifier $ constant "."
                  return (x,y)

schemaRawParser :: Parser SchemaExpRaw'
schemaRawParser = do
        _ <- constant "literal"
        _ <- constant ":"
        t <- typesideExpParser
        schemaLiteral <- (braces $ p t)
        pure $ schemaLiteral
 where p t = do  i <- optional $ do
                    _ <- constant "imports"
                    many schemaExpParser  
                 e <- optional $ do
                    _ <- constant "entities"
                    many identifier
                 f <- optional $ do
                    _ <- constant "foreign_keys"
                    many fkParser
                 p' <- optional $ do
                    _ <- constant "path_equations"
                    many pathEqParser
                 a <- optional $ do
                    _ <- constant "attributes"
                    many attParser
                 o <- optional $ do
                    _ <- constant "observation_equations"
                    many obsEqParser
                 o' <- optional $ do
                    _ <- constant "options"
                    many optionParser
                 pure $ SchemaExpRaw' t
                    (fromMaybe [] e)
                    (concat $ fromMaybe [] f)
                    (concat $ fromMaybe [] a)
                    (fromMaybe [] p')
                    (fromMaybe [] o)
                    (fromMaybe [] o')
                    (fromMaybe [] i)

schemaExpParser :: Parser X.SchemaExp
schemaExpParser =
    SchemaRaw <$> schemaRawParser
    <|>
      SchemaVar <$> identifier
    <|>
       do
        _ <- constant "empty"
        _ <- constant ":"
        x <- typesideExpParser
        return $ SchemaInitial x
    <|> parens schemaExpParser
