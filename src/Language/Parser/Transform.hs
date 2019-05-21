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
module Language.Parser.Transform (transExpParser) where

import           Data.Maybe
import           Language.Parser.Instance
import           Language.Parser.LexerRules
import           Language.Parser.Mapping
import           Language.Parser.Parser
import           Language.Term
import           Language.Transform
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
  m <- braces $ p s t
  pure m
  where
    p s t = do
      i <- optional $ do
        _ <- constant "imports"
        many transExpParser
      e <- optional $ do
        _ <- constant "generators"
        y <- many gParser
        return y
      x <- optional $ do
        _ <- constant "options"
        many optionParser
      pure $ TransExpRaw' s t
        (fromMaybe [] e)
        (fromMaybe [] x)
        (fromMaybe [] i)

sigmaParser' :: Parser TransformExp
sigmaParser' = do
  _ <- constant "sigma"
  f <- mapExpParser
  i <- transExpParser
  o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
  return $ TransformSigma f i $ fromMaybe [] o

sigmaDeltaUnitParser' :: Parser TransformExp
sigmaDeltaUnitParser' = do
  _ <- constant "unit"
  f <- mapExpParser
  i <- instExpParser
  o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
  return $ TransformSigmaDeltaUnit f i $ fromMaybe [] o

sigmaDeltaCoUnitParser' :: Parser TransformExp
sigmaDeltaCoUnitParser' = do
  _ <- constant "counit"
  f <- mapExpParser
  i <- instExpParser
  o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
  return $ TransformSigmaDeltaCoUnit f i $ fromMaybe [] o

deltaParser' :: Parser TransformExp
deltaParser' = do
  _ <- constant "delta"
  f <- mapExpParser
  i <- transExpParser
  o <- optional $ braces $ do { _ <- constant "options"; many optionParser }
  return $ TransformDelta f i $ fromMaybe [] o

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
    x <- instExpParser
    return $ TransformId x

