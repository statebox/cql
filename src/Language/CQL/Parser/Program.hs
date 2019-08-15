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

module Language.CQL.Parser.Program where

import           Data.List
import           Data.Map                       as Map hiding ((\\))
import           Data.Maybe
import           Language.CQL.Common            as C
import           Language.CQL.Parser.Instance   as I
import           Language.CQL.Parser.LexerRules
import           Language.CQL.Parser.Mapping    as M
import           Language.CQL.Parser.Parser
import           Language.CQL.Parser.Schema     as S'
import           Language.CQL.Parser.Transform  as TT
import           Language.CQL.Parser.Typeside   as T'
import           Language.CQL.Program           as P
import           Text.Megaparsec

parseProgram :: String -> Err Prog
parseProgram s = case runParser parseProgram' "" s of
  Left err           -> Left $ "Parse error: " ++ parseErrorPretty err
  Right (opts, prog) -> if length (fst $ unzip prog) == length (nub $ fst $ unzip prog)
    then Right $ toProg opts prog
    else Left  $ "Duplicate definition: " ++ show (nub (fmap fst prog \\ nub (fmap fst prog)))

-- | Returns a list of config option key-value paired with programs.
parseProgram' :: Parser ([(String, String)], [(String, Exp)])
parseProgram' =
  between spaceConsumer eof configsAndProgs
  where
    configsAndProgs = do
      opts  <- optional (constant "options" *> many optionParser)
      progs <- many parseExp
      return (fromMaybe [] opts, progs)

toProg :: [(String, String)] -> [(String, Exp)] -> Prog
toProg _ [] = newProg
toProg opts ((v,e):p) = case e of
  ExpTy ty' -> KindCtx (Map.insert v ty' t) s i m q tr opts
  ExpS s'   -> KindCtx t (Map.insert v s' s)  i m q tr opts
  ExpI i'   -> KindCtx t s (Map.insert v i' i)  m q tr opts
  ExpM m'   -> KindCtx t s i (Map.insert v m' m)  q tr opts
  ExpQ q'   -> KindCtx t s i m (Map.insert v q' q)  tr opts
  ExpT t'   -> KindCtx t s i m q (Map.insert v t' tr)  opts
  where
    KindCtx t s i m q tr _ = toProg opts p

parseExp :: Parser (String, Exp)
parseExp =
  go "typeside"  typesideExpParser ExpTy <|>
  go "schema"    schemaExpParser   ExpS  <|>
  go "instance"  instExpParser     ExpI  <|>
  go "mapping"   mapExpParser      ExpM  <|>
  go "transform" transExpParser    ExpT
  where
    go expKindName bodyParser ctor = do
      _           <- constant expKindName
      expName <- identifier
      _           <- constant "="
      body        <- bodyParser
      return (expName, ctor body)
