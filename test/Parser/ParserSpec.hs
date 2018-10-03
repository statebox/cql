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

  describe "integerParser" $ do
    specify "parses correctly an integer" $
      forAll (arbitrary :: Gen Integer) $ \int ->
        parse integerParser "" (show int) == Right int

  describe "scientificParser" $ do
    specify "parses correctly a scientific number" $
      forAll scientificGen $ \scientific ->
        parse scientificParser "" (show scientific) == Right scientific

  describe "boolParser" $ do
    it "parses correctly a false" $ parse boolParser "" "false" == Right False
    it "parses correctly a true" $ parse boolParser "" "true" == Right True

  -- describe "textParser" $ do
  --   specify "parses correctly any text" $ do
  --     forAll (
  --       fold <$> (listOf $ oneof
  --         [ escapeSeqGen
  --         , (: []) <$> arbitrary `suchThat` (\c -> not (c `elem` ['"', '\r', '\n', '\\']))
  --         ]
  --       )) $ \string ->
  --         parse textParser "" ("\"" ++ string ++ "\"") == Right string

  describe "escapeSeq" $ do
    specify "parses escapable characters" $ do
      forAll (oneof
        [ pure '\b'
        , pure '\t'
        , pure '\n'
        , pure '\f'
        , pure '\r'
        , pure '\''
        , pure '\\'
        , pure '\0'
        , pure '\a'
        , pure '\v'
        ]) $ \char ->
          parse escapeSeq "" (char : []) == Right (char : [])
    specify "parses unicode escaped characters" $ do
      forAll unicodeEscGen $ \unicodeEsc' ->
        parse escapeSeq "" ('\\' : unicodeEsc') == Right ('\\' : unicodeEsc')
    -- it "parses correctly a ." $
    --   parse escapeSeq "" "\\." == Right "\\."

  describe "unicodeEsc" $ do
    it "parses correctly a `u`" $
      parse unicodeEsc "" "u" == Right "u"
    specify "parses correcly a unicode with one digit" $
      forAll hexDigitGen $ \digit ->
        parse unicodeEsc "" ('u' : digit : []) == Right ('u' : digit : [])
    specify "parses correcly a unicode with two digits" $
      forAll ((\a b -> (a, b))
        <$> hexDigitGen
        <*> hexDigitGen
      ) $ \(digit1, digit2) ->
        parse unicodeEsc "" ('u' : digit1 : digit2 : [])
          == Right ('u' : digit1 : digit2 : [])
    specify "parses correcly a unicode with three digits" $
      forAll ((\a b c -> (a, b, c))
        <$> hexDigitGen
        <*> hexDigitGen
        <*> hexDigitGen
      ) $ \(digit1, digit2, digit3) ->
        parse unicodeEsc "" ('u' : digit1 : digit2 : digit3 : [])
          == Right ('u' : digit1 : digit2 : digit3 : [])
