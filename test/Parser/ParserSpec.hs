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
{-# LANGUAGE ScopedTypeVariables #-}

module Parser.ParserSpec where

import           Language.Parser.Generator.Generator
import           Language.Parser.Parser
import           Language.Parser.ReservedWords

-- base
import           Data.Either                         (isLeft)

-- hspec
import           Test.Hspec

-- megaparsec
import           Text.Megaparsec

-- QuickCheck
import           Test.QuickCheck

spec :: Spec
spec = do
  describe "constant" $
    specify "parses correctly a constant" $
    property $ \(anyConstant :: String) ->
      parse (constant anyConstant) "" anyConstant == Right anyConstant

  describe "identifier" $ do
    specify "parses correctly a string starting with a lowercase character" $
      forAll lowerIdGen $ \s -> parse identifier "" s == Right s
    specify "parses correctly a string starting with an uppercase character" $
      forAll upperIdGen $ \s -> parse identifier "" s == Right s
    specify "parses correctly a string starting with a special character" $
      forAll specialIdGen $ \s -> parse identifier "" s == Right s
    specify "does not parse a string starting with a digit" $
      forAll ((:) <$> digitCharGen <*> listOf (oneof [idCharGen, digitCharGen])) $ \s ->
        isLeft $ parse identifier "" s
    specify
      "does not parse a string starting with a not-allowed special character" $
      forAll
        ((:) <$> (elements ['!', '"', '£', '%', '&', '/', '(', ')', '=', '?']) <*>
         listOf (oneof [idCharGen, digitCharGen])) $ \s ->
        isLeft $ parse identifier "" s
    specify "does not parse a reserved word" $
      forAll (elements reservedWords) $ \s -> isLeft $ parse identifier "" s

  describe "boolParser" $ do
    it "parses correctly a false" $ parse boolParser "" "false" == Right False
    it "parses correctly a true" $ parse boolParser "" "true" == Right True
