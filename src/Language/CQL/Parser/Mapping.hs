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
module Language.CQL.Parser.Mapping where

import           Language.CQL.Mapping
import           Language.CQL.Parser.LexerRules
import           Language.CQL.Parser.Parser
import           Language.CQL.Parser.Schema     hiding (attParser, fkParser)
import           Language.CQL.Term

-- megaparsec
import           Text.Megaparsec

-- prelude
import           Data.Maybe

--------------------------------------------------------------------------------

fkParser :: Parser (String, [String])
fkParser = do
  x <- identifier
  _ <- constant "->"
  y <- sepBy1 identifier $ constant "."
  return (x, y)

attParser :: Parser (String, Either (String, Maybe String, RawTerm) [String])
attParser = do
  x <- identifier
  _ <- constant "->"
  c1 x <|> c2 x
  where
    c1 x = do
      _ <- constant "lambda"
      y <- identifier
      z <- optional $ do
        _ <- constant ":"
        identifier
      _ <- constant "."
      e <- rawTermParser
      return (x, Left (y, z, e))
    c2 x = do
      y <- sepBy1 identifier $ constant "."
      return (x, Right y)

mapCompParser :: Parser MappingExp
mapCompParser = do
  _ <- constant "["
  f <- mapExpParser
  _ <- constant ";"
  g <- mapExpParser
  _ <- constant "]"
  return $ MappingComp f g

mappingRawParser :: Parser MappingExpRaw'
mappingRawParser = do
  _ <- constant "literal"
  _ <- constant ":"
  s <- schemaExpParser
  _ <- constant "->"
  t <- schemaExpParser
  braces $ q' s t
  where
    p = do
      x <- do
        _ <- constant "entity"
        v <- identifier
        _ <- constant "->"
        u <- identifier
        return (v, u)
      f <- optional $ do
        _ <- constant "foreign_keys"
        many fkParser
      a <- optional $ do
        _ <- constant "attributes"
        many attParser
      pure (x, fromMaybe [] f, fromMaybe [] a)
    q' s t = do
      i <- optional $ do
        _ <- constant "imports"
        many mapExpParser
      m <- many p
      o <- optional $ do
        _ <- constant "options"
        many optionParser
      pure $ q s t (fromMaybe [] o) (fromMaybe [] i) m
    q s t o i = Prelude.foldr
      (\(x,fm,am) (MappingExpRaw' s' t' ens' fks' atts' o' i') -> MappingExpRaw' s' t' (x:ens') (fm++fks') (am++atts') o' i')
      (MappingExpRaw' s t [] [] [] o i)


mapExpParser :: Parser MappingExp
mapExpParser
  =   mapCompParser
  <|> MappingRaw <$> mappingRawParser
  <|> MappingVar <$> identifier
  <|> parens mapExpParser
  <|> do
    _ <- constant "identity"
    MappingId <$> schemaExpParser

