module Language.Parser.Generator.Generator where

import           Language.Parser.ReservedWords

-- base
import           Control.Applicative ((<|>))

-- QuickCheck
import           Test.QuickCheck.Gen

lowerCharGen :: Gen Char
lowerCharGen = elements ['a' .. 'z']

upperCharGen :: Gen Char
upperCharGen = elements ['A' .. 'Z']

idCharGen :: Gen Char
idCharGen = oneof
    [ lowerCharGen
    , upperCharGen
    , elements ['_', '$']
    ]

digitCharGen :: Gen Char
digitCharGen = elements ['0' .. '9']

upperIdGen :: Gen String
upperIdGen = (:) <$> upperCharGen <*> listOf (oneof [idCharGen, digitCharGen])

lowerIdGen :: Gen String
lowerIdGen = (:) <$> lowerCharGen <*> listOf (oneof [idCharGen, digitCharGen])

specialIdGen :: Gen String
specialIdGen = (:) <$> idCharGen <*> listOf (oneof [idCharGen, digitCharGen])

identifierGen :: Gen String
identifierGen = (oneof
    [ lowerIdGen
    , upperIdGen
    , specialIdGen
    ]) `suchThat` (\s -> not (s `elem` reservedWords))