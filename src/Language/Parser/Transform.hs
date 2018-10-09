module Language.Parser.Transform where

import           Data.Maybe
import           Language.Transform
import           Text.Megaparsec

import           Language.Parser.Instance
import           Language.Parser.LexerRules
import           Language.Parser.Parser
import           Language.Term


gParser :: Parser (String, RawTerm)
gParser = do x <- identifier
             _ <- constant "->"
             e <- rawTermParser
             return (x, e)

transformRawParser :: Parser TransExpRaw'
transformRawParser = do
        _ <- constant "literal"
        _ <- constant ":"
        s <- instExpParser
        _ <- constant "->"
        t <- instExpParser
        m <- braces $ p s t
        pure m
 where p s t  = do  e <- optional $ do
                      _ <- constant "generators"
                      y <- many gParser
                      return y
                    x <- optional $ do
                      _ <- constant "options"
                      many optionParser
                    pure $ TransExpRaw' s t
                      (fromMaybe [] e)
                      (fromMaybe [] x)




transExpParser :: Parser TransformExp
transExpParser =
    TransformRaw <$> transformRawParser
    <|>
      TransformVar <$> identifier
    <|>
       do
        _ <- constant "identity"
        x <- instExpParser
        return $ TransformId x
