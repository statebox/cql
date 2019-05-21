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
module Language.Parser.Parser where

import           Language.Parser.LexerRules
import           Language.Parser.ReservedWords

-- base
import           Data.Char

-- megaparsec
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

-- scientific
import           Data.Scientific               (Scientific)
import           Language.Term

rawTermParser :: Parser RawTerm
rawTermParser =
  try (do f <- identifier
          _ <- constant "("
          a <- sepBy rawTermParser $ constant ","
          _ <- constant ")"
          return $ RawApp f a)
  <|>
  try (do t <- sepBy1 identifier $ constant "."
          return $ Prelude.foldl (\y x -> RawApp x [y]) (RawApp (head t) []) $ tail t)
  <|>
  try (do i <- identifier
          return $ RawApp i [])
  <|>
  try (do _ <- constant "("
          a <- rawTermParser
          f <- identifier
          b <- rawTermParser
          _ <- constant ")"
          return $ RawApp f [a, b])

optionParser :: Parser (String, String)
optionParser =
  do i <- identifier
     _ <- constant "="
     j <- identifier
     return (i, j)

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    unquotedIdentifier = lowerId <|> upperId <|> specialId
    quotedIdentifier   = between (char '"') (char '"') $ some $ satisfy (\c -> isPrint c && (c /= '"'))
    p = unquotedIdentifier <|> quotedIdentifier
    check x =
      if x `elem` reservedWords
        then fail $ "keyword" ++ show x ++ "cannot be used as an identifier"
        else return x

constant :: String -> Parser String
constant = L.symbol spaceConsumer

braces :: Parser a -> Parser a
braces = between (constant "{") (constant "}")

parens :: Parser a -> Parser a
parens = between (constant "(") (constant ")")

integerParser :: Parser Integer -- TODO: write tests
integerParser = lexeme L.decimal

scientificParser :: Parser Scientific -- TODO: write tests
scientificParser = lexeme L.scientific

boolParser :: Parser Bool -- TODO: write tests
boolParser
  = pure True <* constant "true"
  <|> pure False <* constant "false"

textParser :: Parser String -- TODO: write tests
textParser = do
  _ <- constant "\""
  text <- many (escapeSeq <|> show <$> noneOf ['"', '\r', '\n', '\\']) -- TODO: check if the escping is correct
  _ <- constant "\""
  pure $ unwords text

escapeSeq :: Parser String -- TODO: write tests
escapeSeq = do
  _ <- char '\\'
  escaped
    <- show <$> oneOf ['b', 't', 'n', 'f', 'r', '"', '\'', '\\', '.']
    <|> unicodeEsc
    <|> eof *> pure ""
  pure escaped

unicodeEsc :: Parser String -- TODO: write tests
unicodeEsc
  = char 'u' *> pure "u"
  <|> (:)
    <$> (char 'u')
    <*> (show <$> hexDigitChar)
  <|> (:)
    <$> (char 'u')
    <*> ((:) <$> hexDigitChar <*> (show <$> hexDigitChar))
  <|> (:)
    <$> (char 'u')
    <*>((:)
      <$> hexDigitChar
      <*> ((:) <$> hexDigitChar <*> (show <$> hexDigitChar)))
