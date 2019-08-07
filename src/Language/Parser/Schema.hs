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

module Language.Parser.Schema where

import           Language.Parser.LexerRules
import           Language.Parser.Parser
import           Language.Parser.Typeside
import           Language.Schema            as X
import           Language.Term
import           Language.Typeside

-- base
import           Data.Maybe

-- megaparsec
import           Text.Megaparsec

obsEqParser :: Parser (String, Maybe String, RawTerm, RawTerm)
obsEqParser = do
  _ <- constant "forall"
  i <- identifier
  j <- optional $ do { _ <- constant ":"; identifier }
  _ <- constant "."
  l <- rawTermParser
  _ <- constant "="
  r <- rawTermParser
  return (i, j, l, r)

attParser :: Parser [(Att, (En, Ty))]
attParser = fkParser

fkParser :: Parser [(Fk, (En, En))]
fkParser = do
  x <- some identifier
  _ <- constant ":"
  y <- identifier
  _ <- constant "->"
  z <- identifier
  return $ map (, (y, z)) x

pathEqParser :: Parser ([Fk],[Fk])
pathEqParser = do
  x <- sepBy1 identifier $ constant "."
  _ <- constant "="
  y <- sepBy1 identifier $ constant "."
  return (x, y)

schemaRawParser :: Parser SchemaExpRaw'
schemaRawParser = do
  _ <- constant "literal"
  _ <- constant ":"
  t <- typesideExpParser
  braces $ p t
  where
    p t = do
      i <- optional $ do
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
        (fromMaybe [] o )
        (fromMaybe [] o')
        (fromMaybe [] i )

schemaExpParser :: Parser X.SchemaExp
schemaExpParser
  =   SchemaRaw <$> schemaRawParser
  <|> SchemaVar <$> identifier
  <|> do
    _ <- constant "empty"
    _ <- constant ":"
    SchemaInitial <$> typesideExpParser
  <|> parens schemaExpParser
