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
