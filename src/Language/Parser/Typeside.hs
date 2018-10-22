module Language.Parser.Typeside where

import           Data.Maybe
import           Language.Parser.LexerRules
import           Language.Parser.Parser
import           Language.Term

-- megaparsec
import           Language.Typeside          as X
import           Text.Megaparsec

typesideExpParser :: Parser TypesideExp
typesideExpParser = parseRaw <|> parseEmpty <|> parseVar <|> parens typesideExpParser

parseEmpty :: Parser TypesideExp
parseEmpty = do _ <- constant "empty"
                return TypesideInitial

--parseSql = do _ <- constant "sql"
 --             return TypesideSql

parseVar :: Parser TypesideExp
parseVar = do x <- identifier
              return $ TypesideVar x

parseRaw :: Parser TypesideExp
parseRaw = do _ <- constant "literal"
              tsLiteral <- (braces typesideLiteralSectionParser)
              pure $ TypesideRaw $ tsLiteral

eqParser :: Parser ([(String, Maybe String)], RawTerm, RawTerm)
eqParser = do o <- p
              l <- rawTermParser
              _ <- constant "="
              r <- rawTermParser
              return (o,l,r) --(fromMaybe [] o, l, r)
 where p = do _ <- constant "forall"
              g <- sepBy varParser $ constant "," 
              _ <- constant "."
              return $ concat g


varParser :: Parser [(String, Maybe String)]
varParser = do x <- some identifier
               y <- optional $ do _ <- constant ":"
                                  identifier
               return $ map (\a -> (a,y)) x

constantParser :: Parser [(String, ([String], String))]
constantParser = do x <- some identifier
                    _ <- constant ":"
                    y <- identifier
                    return $ map (\a -> (a,([],y))) x

functionParser :: Parser [(String, ([String], String))]
functionParser = do x <- some identifier
                    _ <- constant ":"
                    y <- sepBy identifier $ constant ","
                    _ <- constant "->"
                    z <- identifier
                    return $ map (\a -> (a,(y,z))) x

typesideLiteralSectionParser :: Parser X.TypesideRaw'
typesideLiteralSectionParser = do
    i <- optional $ do
        _ <- constant "imports"
        many typesideExpParser  
    t <- optional $ do
        _ <- constant "types"
        many identifier
    c <- optional $ do
        _ <- constant "constants"
        many constantParser
    f <- optional $ do
        _ <- constant "functions"
        many functionParser
    e <- optional $ do
        _ <- constant "equations"
        many eqParser
    o <- optional $ do
        _ <- constant "options"
        many optionParser
    pure $ TypesideRaw'
        (fromMaybe [] t)
        ((concat $ fromMaybe [] c)++(concat $ fromMaybe [] f))
        (fromMaybe [] e)
        (fromMaybe [] o)
        (fromMaybe [] i)

