{-
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `statebox/cql`, the categorical query language.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
-}

{-# LANGUAGE TupleSections #-}

module Language.CQL.Parser.Typeside where

import           Language.CQL.Parser.LexerRules
import           Language.CQL.Parser.Parser
import           Language.CQL.Term
import           Language.CQL.Typeside          as X

-- base
import           Data.Maybe

-- megaparsec
import           Text.Megaparsec

typesideExpParser :: Parser TypesideExp
typesideExpParser
  =   parseSql
  <|> parseRaw
  <|> parseEmpty
  <|> parseVar
  <|> parens typesideExpParser

parseEmpty :: Parser TypesideExp
parseEmpty = do
  _ <- constant "empty"
  return TypesideInitial

parseSql :: Parser TypesideExp
parseSql = do
  _ <- constant "sql"
  return TypesideSql

parseVar :: Parser TypesideExp
parseVar = TypesideVar <$> identifier

parseRaw :: Parser TypesideExp
parseRaw = do
  _ <- constant "literal"
  TypesideRaw <$> braces typesideLiteralSectionParser

eqParser :: Parser ([(String, Maybe String)], RawTerm, RawTerm)
eqParser = do
  o <- p
  l <- rawTermParser
  _ <- constant "="
  r <- rawTermParser
  return (o, l, r)
  where
    p = do
        _ <- constant "forall"
        g <- sepBy varParser $ constant ","
        _ <- constant "."
        return $ concat g
      <|> return []

varParser :: Parser [(String, Maybe String)]
varParser = do
  x <- some identifier
  y <- optional $ do { _ <- constant ":" ; identifier }
  return $ map (, y) x

constantParser :: Parser [(String, ([String], String))]
constantParser = do
  x <- some identifier
  _ <- constant ":"
  y <- identifier
  return $ map (, ([] ,y)) x

functionParser :: Parser [(String, ([String], String))]
functionParser = do
  x <- some identifier
  _ <- constant ":"
  y <- sepBy identifier $ constant ","
  _ <- constant "->"
  z <- identifier
  return $ map (, (y, z)) x

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
    (concat (fromMaybe [] c) ++ concat (fromMaybe [] f))
    (fromMaybe [] e)
    (fromMaybe [] o)
    (fromMaybe [] i)
