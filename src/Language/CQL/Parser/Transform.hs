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
module Language.CQL.Parser.Transform (transExpParser) where

import           Language.CQL.Instance
import           Language.CQL.Mapping
import           Language.CQL.Parser.Instance
import           Language.CQL.Parser.LexerRules
import           Language.CQL.Parser.Mapping
import           Language.CQL.Parser.Parser
import           Language.CQL.Term
import           Language.CQL.Transform

-- prelude
import           Data.Maybe

-- megaparsec
import           Text.Megaparsec


gParser :: Parser (String, RawTerm)
gParser = do
  x <- identifier
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
  braces $ p s t
  where
    p s t = do
      i <- optional $ do
        _ <- constant "imports"
        many transExpParser
      e <- optional $ do
        _ <- constant "generators"
        many gParser
      x <- optional $ do
        _ <- constant "options"
        many optionParser
      pure $ TransExpRaw' s t
        (fromMaybe [] e)
        (fromMaybe [] x)
        (fromMaybe [] i)

mapTransParser :: String -> (MappingExp -> TransformExp -> [(String, String)] -> TransformExp) -> Parser TransformExp
mapTransParser s constructor = do
  _ <- constant s
  f <- mapExpParser
  i <- transExpParser
  o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
  return $ constructor f i $ fromMaybe [] o

mapInstTransParser :: String -> (MappingExp -> InstanceExp -> [(String, String)] -> TransformExp) -> Parser TransformExp
mapInstTransParser s constructor = do
  _ <- constant s
  f <- mapExpParser
  i <- instExpParser
  o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
  return $ constructor f i $ fromMaybe [] o

sigmaParser' :: Parser TransformExp
sigmaParser' = mapTransParser "sigma" TransformSigma

sigmaDeltaUnitParser' :: Parser TransformExp
sigmaDeltaUnitParser' = mapInstTransParser "unit" TransformSigmaDeltaUnit

sigmaDeltaCoUnitParser' :: Parser TransformExp
sigmaDeltaCoUnitParser' = mapInstTransParser "counit" TransformSigmaDeltaCoUnit

deltaParser' :: Parser TransformExp
deltaParser' = mapTransParser "delta" TransformDelta

transCompParser :: Parser TransformExp
transCompParser = do
  _ <- constant "["
  f <- transExpParser
  _ <- constant ";"
  g <- transExpParser
  _ <- constant "]"
  return $ TransformComp f g

transExpParser :: Parser TransformExp
transExpParser = transCompParser
  <|> TransformRaw <$> transformRawParser
  <|> TransformVar <$> identifier
  <|> sigmaParser'
  <|> deltaParser'
  <|> sigmaDeltaUnitParser'
  <|> sigmaDeltaCoUnitParser'
  <|> parens transExpParser
  <|> do
    _ <- constant "identity"
    TransformId <$> instExpParser

