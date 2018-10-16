module Language.Parser.Transform where

import           Data.Maybe
import           Language.Transform
import           Text.Megaparsec

import           Language.Parser.Instance
import           Language.Parser.LexerRules
import           Language.Parser.Mapping
import           Language.Parser.Parser
import           Language.Term


gParser :: Parser (String, RawTerm)
gParser = do x <- identifier
             _ <- constant "->"
             e <- optionalParens rawTermParser
             return (x, e)

transformRawParser :: Parser TransExpRaw'
transformRawParser = do
        _ <- constant "literal"
        _ <- constant ":"
        s <- optionalParens instExpParser
        _ <- constant "->"
        t <- optionalParens instExpParser
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


sigmaParser' :: Parser TransformExp
sigmaParser' = do _ <- constant "sigma"
                  f <- optionalParens mapExpParser
                  i <- optionalParens transExpParser
                  o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
                  return $ TransformSigma f i $ fromMaybe [] o

sigmaDeltaUnitParser' :: Parser TransformExp
sigmaDeltaUnitParser' = do _ <- constant "unit"
                           f <- optionalParens mapExpParser
                           i <- optionalParens instExpParser
                           o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
                           return $ TransformSigmaDeltaUnit f i $ fromMaybe [] o


sigmaDeltaCoUnitParser' :: Parser TransformExp
sigmaDeltaCoUnitParser' = do _ <- constant "counit"
                             f <- optionalParens mapExpParser
                             i <- optionalParens instExpParser
                             o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
                             return $ TransformSigmaDeltaCoUnit f i $ fromMaybe [] o


deltaParser' :: Parser TransformExp
deltaParser' = do _ <- constant "delta"
                  f <- optionalParens mapExpParser
                  i <- optionalParens transExpParser
                  o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
                  return $ TransformDelta f i $ fromMaybe [] o

transExpParser :: Parser TransformExp
transExpParser =
    TransformRaw <$> transformRawParser
    <|>
      TransformVar <$> identifier

    <|> sigmaParser' <|> deltaParser' <|> sigmaDeltaUnitParser' <|> sigmaDeltaCoUnitParser' <|>
       do
        _ <- constant "identity"
        x <- optionalParens instExpParser
        return $ TransformId x
