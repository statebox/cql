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
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitForAll        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImpredicativeTypes    #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.Program where

import           Control.DeepSeq
import           Data.Map.Strict    as Map
import           Language.Common    (section, TyMap, Kind(..))
import           Language.Instance  as I
import           Language.Mapping   as M
import           Language.Query     as Q
import           Language.Schema    as S
import           Language.Term      as Term
import           Language.Transform as Tr
import           Language.Typeside  as T
import           Prelude            hiding (EQ)

-- | Top level CQL expressions, untyped.
data Exp
  = ExpTy TypesideExp
  | ExpS  SchemaExp
  | ExpI  InstanceExp
  | ExpM  MappingExp
  | ExpT  TransformExp
  | ExpQ  QueryExp

-- | Top level CQL expressions, dynamically typed.
data Val
  = ValTy TypesideEx
  | ValS  SchemaEx
  | ValI  InstanceEx
  | ValM  MappingEx
  | ValT  TransformEx
  | ValQ  QueryEx
  deriving Show

instance NFData Val where
  rnf v = case v of
    ValTy x -> rnf x
    ValS  x -> rnf x
    ValI  x -> rnf x
    ValM  x -> rnf x
    ValT  x -> rnf x
    ValQ  x -> rnf x

-- | Isomorphic to @Ctx (String + ... + String) (ts + ... + t)@.
data KindCtx ts s i m q t o
  = KindCtx
  { typesides  :: Ctx String ts
  , schemas    :: Ctx String s
  , instances  :: Ctx String i
  , mappings   :: Ctx String m
  , queries    :: Ctx String q
  , transforms :: Ctx String t
  , other      :: o
  }

-- | A CQL program.
type Prog = KindCtx TypesideExp SchemaExp InstanceExp MappingExp QueryExp TransformExp [(String, String)]

newProg :: KindCtx ts s i m q t [a]
newProg = newEnv []

-- | The result of an CQL type checking pass.
type Types = KindCtx TypesideExp TypesideExp SchemaExp (SchemaExp,SchemaExp) (SchemaExp,SchemaExp) (InstanceExp,InstanceExp) ()

newTypes :: KindCtx ts s i m q t ()
newTypes = newEnv ()

newEnv :: o -> KindCtx ts s i m q t o
newEnv = KindCtx m m m m m m
  where m = Map.empty

instance TyMap Show '[ts, s, i, m, q, t, o] => Show (KindCtx ts s i m q t o) where
  show (KindCtx ts s i m q t o) =
    section "program" $ unlines
      [ section "typesides"  $ showCtx ts
      , section "schemas"    $ showCtx s
      , section "instances"  $ showCtx i
      , section "mappings"   $ showCtx m
      , section "queries"    $ showCtx q
      , section "transforms" $ showCtx t
      , section "other"      $ show o
      ]
    where
      showCtx :: (Show a1, Show a2) => Map a1 a2 -> String
      showCtx m = unlines $ (\(k,v) -> show k ++ " = " ++ show v ++ "\n") <$> Map.toList m

allVars :: KindCtx ts s i m q t o -> [(String, Kind)]
allVars ctx =
  (fmap (, TYPESIDE ) . keys . typesides  $ ctx) <>
  (fmap (, SCHEMA   ) . keys . schemas    $ ctx) <>
  (fmap (, INSTANCE ) . keys . instances  $ ctx) <>
  (fmap (, MAPPING  ) . keys . mappings   $ ctx) <>
  (fmap (, QUERY    ) . keys . queries    $ ctx) <>
  (fmap (, TRANSFORM) . keys . transforms $ ctx)
