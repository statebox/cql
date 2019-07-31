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
{-# LANGUAGE FlexibleContexts, OverloadedLists, OverloadedStrings, TupleSections #-}
module Language.Congruence (decide, Term(Function)) where

import           Prelude hiding (any)

import           Control.Monad hiding (unless)
import           Control.Monad.Trans.UnionFind (runUnionFind,UnionFindT)
--import qualified Control.Monad.Trans.UnionFind as U
--import           Control.Monad.Writer hiding (unless)

--import           Data.Sequence (Seq)
import           Data.Foldable (traverse_)
--import           Data.Text (Text)
--import qualified Data.Map as M
import           Data.Graph.Inductive (LNode)
import           Data.Functor.Identity

import           Language.Internal


decide :: Ord t => [(Term t, Term t)] -> Term t -> Term t -> Bool
decide theory lhs rhs = not result
  where
    conjunctions = fmap (uncurry Equal) theory
    Identity result = hasModel (Conjunction $ NotEqual lhs rhs : conjunctions)


hasModel :: Ord t => Monad m => Conjunctions t -> m Bool
hasModel (Conjunction conjunctions) = runUnionFind $ do
  gr <- termGraph conjunctions
  let (pos,neg) = partition gr positive conjunctions
  traverse_ (merge gr) pos

  anyEquiv <- any equivalent neg
  pure $ not anyEquiv


merge :: Monad m => Graph t -> (Vert t, Vert t) -> UnionFindT (LNode t) m ()
merge gr (u,v) =
  unless (equivalent u v) $ do
    pu <- predOfAllVertEquivTo u
    pv <- predOfAllVertEquivTo v
    u `union` v
    needMerging <- filterM (notEquivalentButCongruent gr)
                           [ (x,y) | x <- pu, y <- pv ]
    traverse_ (merge gr) needMerging
  where
    predOfAllVertEquivTo vert =
      concatMap (predecessors gr) <$> filterM (equivalent vert) (vertices gr)

notEquivalentButCongruent :: (Monad m) => Graph t -> (Vert t, Vert t) -> UnionFindT (LNode t) m Bool
notEquivalentButCongruent gr (x,y) = do
  notEquiv <- not <$> equivalent x y
  cong <- congruent gr x y
  return $ notEquiv && cong

-- testing
congruent :: (Monad m) => Graph t -> Vert t -> Vert t -> UnionFindT (LNode t) m Bool
congruent gr x y =
  if outDegree gr x /= outDegree gr y
  then return False
  else and <$> zipWithM equivalent (successors gr x) (successors gr y)

{--
constructModel :: Monad m => Graph -> UnionFindT (LNode Text) m Satisfiability
constructModel g@(Graph (_,gr)) = do
  psi <- forM (labNodes gr) $ \v@(_,(_,vp)) -> do
    rp <- U.repr vp
    (rn,rt) <- U.descriptor rp
    return (term g (Vert v), term g (Vert (rn,(rt,rp))))
  return $ Satisfiable (M.fromList psi)
--}

{--

  Copyright (c) 2014, Sven Keidel

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

    * Neither the name of Sven Keidel nor the names of other
      contributors may be used to endorse or promote products derived
      from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

--}