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
module Language.Parser.Generator.Generator where

import           Language.Parser.ReservedWords

-- QuickCheck
import           Test.QuickCheck.Gen

-- BASIC
lowerCharGen :: Gen Char
lowerCharGen = elements ['a' .. 'z']

upperCharGen :: Gen Char
upperCharGen = elements ['A' .. 'Z']

idCharGen :: Gen Char
idCharGen = oneof [lowerCharGen, upperCharGen, elements ['_', '$']]

digitCharGen :: Gen Char
digitCharGen = elements ['0' .. '9']

upperIdGen :: Gen String
upperIdGen =
  ((:) <$> upperCharGen <*>
    listOf (oneof [idCharGen, digitCharGen])) `suchThat`
      (`notElem` reservedWords)

lowerIdGen :: Gen String
lowerIdGen =
  ((:) <$> lowerCharGen <*>
    listOf (oneof [idCharGen, digitCharGen])) `suchThat`
      (`notElem` reservedWords)

specialIdGen :: Gen String
specialIdGen = (:) <$> idCharGen <*> listOf (oneof [idCharGen, digitCharGen])

identifierGen :: Gen String
identifierGen = oneof [lowerIdGen, upperIdGen, specialIdGen]

boolGen :: Gen Bool
boolGen = oneof [pure True, pure False]
