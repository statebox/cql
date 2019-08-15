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

module Language.CQL.Graph where

import           Prelude

data Graph a = Graph { vertices :: [a], edges :: [(a, a)] } deriving Show

removeEdge :: (Eq a) => (a, a) -> Graph a -> Graph a
removeEdge x (Graph v e) = Graph v (filter (/=x) e)

connections :: (Eq a) => ((a, a) -> a) -> a -> Graph a -> [(a, a)]
connections f0 x (Graph _ e) = filter ((==x) . f0) e

outbound :: Eq b => b -> Graph b -> [(b, b)]
outbound = connections fst

inbound :: Eq a => a -> Graph a -> [(a, a)]
inbound = connections snd

-- | Topological sort.
tsort :: (Eq a) => Graph a -> Either String [a]
tsort graph  = tsort' [] (noInbound graph) graph
  where
    noInbound (Graph v e) = filter (flip notElem $ fmap snd e) v
    tsort' l []    (Graph _ []) = pure $ reverse l
    tsort' _ []    _            = Left "There is at least one cycle in the graph."
    tsort' l (n:s) g            = tsort' (n:l) s' g'
      where
        outEdges = outbound n g
        outNodes = snd <$> outEdges
        g'       = foldr removeEdge g outEdges
        s'       = s ++ filter (null . flip inbound g') outNodes
