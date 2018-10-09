module Language.Parser.Instance where

import           Language.Parser.LexerRules
import           Language.Parser.Parser

-- base
import           Data.Maybe

-- megaparsec
import           Text.Megaparsec

import           Language.Instance          as I
import           Language.Parser.Schema
import           Language.Schema            as S
import           Language.Term

eqParser :: Parser (RawTerm, RawTerm)
eqParser = do l <- rawTermParser
              _ <- constant "="
              r <- rawTermParser
              return (l,r)


skParser :: Parser [(Gen, En)]
skParser = genParser


genParser :: Parser [(Gen, En)]
genParser = do x <- some identifier
               _ <- constant ":"
               y <- identifier
               return $ map (\a -> (a,y)) x


instRawParser :: Parser InstExpRaw'
instRawParser = do
        _ <- constant "literal"
        _ <- constant ":"
        t <- schemaExpParser
        x <- (braces $ p t)
        pure $ x
 where p t = do  e <- optional $ do
                    _ <- constant "generators"
                    y <- many genParser
                    return $ concat y
                 o <- optional $ do
                    _ <- constant "equations"
                    many eqParser
                 x <- optional $ do
                    _ <- constant "options"
                    many optionParser
                 pure $ InstExpRaw' t
                    (fromMaybe [] e)
                    (fromMaybe [] o)
                    (fromMaybe [] x)

instExpParser :: Parser InstanceExp
instExpParser =
    InstanceRaw <$> instRawParser
    <|>
      InstanceVar <$> identifier
    <|>
       do
        _ <- constant "empty"
        _ <- constant ":"
        x <- schemaExpParser
        return $ InstanceInitial x
