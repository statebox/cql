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
module Language.Parser where

import           Data.List
import           Data.Map                   as Map hiding ((\\))
import           Data.Maybe
import           Language.Common            as C
import           Language.Parser.Instance   as I
import           Language.Parser.LexerRules
import           Language.Parser.Mapping    as M
import           Language.Parser.Parser
import           Language.Parser.Schema     as S'
import           Language.Parser.Transform  as TT
import           Language.Parser.Typeside   as T'
import           Language.Program           as P
import           Text.Megaparsec

parseCqlProgram' :: Parser (String, Exp)
parseCqlProgram' = do
  _ <- constant "typeside"
  x <- identifier
  _ <- constant "="
  y <- typesideExpParser
  return (x, ExpTy y)
  <|>
  do
    _ <- constant "schema"
    x <- identifier
    _ <- constant "="
    y <- schemaExpParser
    return (x, ExpS y)
  <|>
  do
    _ <- constant "instance"
    x <- identifier
    _ <- constant "="
    y <- instExpParser
    return (x, ExpI y)
  <|>
  do
    _ <- constant "mapping"
    x <- identifier
    _ <- constant "="
    y <- mapExpParser
    return (x, ExpM y)
  <|>
  do
    _ <- constant "transform"
    x <- identifier
    _ <- constant "="
    y <- transExpParser
    return (x, ExpT y)

parseCqlProgram'' :: Parser ([(String,String)],[(String, Exp)])
parseCqlProgram'' = between spaceConsumer eof g
  where
    f = do
      _ <- constant "options"
      many optionParser
    g = do
      x <- optional f
      y <- many parseCqlProgram'
      return (fromMaybe [] x, y)


toProg' :: [(String, String)] -> [(String, Exp)] -> Prog
toProg' _ [] = newProg
toProg' o ((v,e):p) = case e of
   ExpTy ty' -> KindCtx (Map.insert v ty' t) s i m q tr o
   ExpS s'   -> KindCtx t (Map.insert v s' s) i m q tr o
   ExpI i'   -> KindCtx t s (Map.insert v i' i) m q tr o
   ExpM m'   -> KindCtx t s i (Map.insert v m' m) q tr o
   ExpQ q'   -> KindCtx t s i m (Map.insert v q' q) tr o
   ExpT t'   -> KindCtx t s i m q (Map.insert v t' tr) o
  where KindCtx t s i m q tr _ = toProg' o p

parseCqlProgram :: String -> Err Prog
parseCqlProgram s = case runParser parseCqlProgram'' "" s of
  Left err -> Left $ "Parse error: " ++ (parseErrorPretty err)
  Right (o, x) -> if length (fst $ unzip x) == length (nub $ fst $ unzip x)
    then pure $ toProg' o x
    else Left $ "Duplicate definition: " ++ show (nub (fmap fst x \\ nub (fmap fst x)))
