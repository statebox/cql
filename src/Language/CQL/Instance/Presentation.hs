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
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.CQL.Instance.Presentation where

import           Control.DeepSeq       (deepseq, NFData(..))
import           Data.Map.Strict       (Map)
import qualified Data.Map.Strict       as Map
import           Data.Maybe            ()
import           Data.Set              (Set)
import qualified Data.Set              as Set
import           Data.Void
import           Language.CQL.Collage  (Collage(..), typeOfCol)
import           Language.CQL.Common   (Err, MultiTyMap, TyMap, type (+), section, sepTup, intercalate)
import           Language.CQL.Schema   (Schema, schToCol)
import           Language.CQL.Term     as Term
import           Prelude               hiding (EQ)

-- | A presentation of an @Instance@.
data Presentation var ty sym en fk att gen sk
  = Presentation
  { gens :: Map gen en
  , sks  :: Map sk ty
  , eqs  :: Set (EQ Void ty sym en fk att gen sk)
  }

instance TyMap Show '[var, ty, sym, en, fk, att, gen, sk]
  => Show (Presentation var ty sym en fk att gen sk) where
  show (Presentation ens' _ eqs') =
    unlines
      [ section "generators" $ intercalate "\n" $ sepTup " : " <$> Map.toList ens'
      , section "equations"  $ intercalate "\n" $ Set.map show eqs'
      ]

instance (NFData ty, NFData sym, NFData en, NFData fk, NFData att, NFData gen, NFData sk)
  => NFData (Presentation var ty sym en fk att gen sk) where
  rnf (Presentation g s e) = deepseq g $ deepseq s $ rnf e

-- | Checks that an instance presentation is a well-formed theory.
typecheckPresentation
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, gen, sk])
  => Schema var ty sym en fk att
  -> Presentation var ty sym en fk att gen sk
  -> Err ()
typecheckPresentation sch p = typeOfCol $ presToCol sch p

--created as an alias because of name clashes
eqs0
  :: Presentation var  ty sym en fk att gen sk
  -> Set (EQ      Void ty sym en fk att gen sk)
eqs0 (Presentation _ _ x) = x

-- | Converts a presentation to a collage.
presToCol
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, gen, sk])
  => Schema var ty sym en fk att
  -> Presentation var ty sym en fk att gen sk
  -> Collage (()+var) ty sym en fk att gen sk
presToCol sch (Presentation gens' sks' eqs') =
 Collage (Set.union e1 e2) (ctys schcol)
         (cens schcol) (csyms schcol) (cfks schcol) (catts schcol) gens' sks'
  where
    schcol = schToCol sch
    e1 = Set.map (\(   EQ (l,r)) -> (Map.empty, EQ (upp l, upp r)))   eqs'
    e2 = Set.map (\(g, EQ (l,r)) -> (g,         EQ (upp l, upp r))) $ ceqs schcol
