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
{-# LANGUAGE ViewPatterns
           , FlexibleContexts
           , FlexibleInstances
           , TypeFamilies
           , UndecidableInstances
           , MultiParamTypeClasses
           , FunctionalDependencies
#-}
module Language.CQL.Internal where

import           Prelude                       hiding (abs, any)

import           Control.Arrow
import           Control.Monad
import           Control.Monad.Trans.UnionFind (Point, UnionFindT, fresh)
import qualified Control.Monad.Trans.UnionFind as U

import qualified Data.List                     as L
--import           Data.Sequence (Seq)
import           Data.Foldable                 (traverse_)
import           Data.Graph.Inductive          hiding (Graph)
import           Data.Map                      (Map)
import           Data.Maybe                    (fromJust)
import           Data.Traversable              (traverse)




newtype Conjunctions t = Conjunction [Equation t]
data Equation t
  =    Equal (Term t) (Term t)
  | NotEqual (Term t) (Term t)
data Term t = Function t [Term t]
  deriving (Eq, Ord)

data Satisfiability t = Satisfiable (Model t) | Unsatisfiable
  deriving (Show, Eq)

type Model t = Map (Term t) (Term t)

(===) :: Term t -> Term t -> Equation t
(===) = Equal
infix 4 ===

(=/=) :: Term t -> Term t -> Equation t
(=/=) = NotEqual
infix 4 =/=

instance Show t => Show (Term t) where
  show (Function sym childs) =
    show sym ++ "(" ++ L.intercalate "," (map show childs) ++ ")"

class Conjunction t a | a -> t where
  (/\) :: Equation t -> a -> Conjunctions t
  infixr 3 /\

instance (Conjunction t (Equation t)) where
  (/\) e1 e2 = Conjunction [e1, e2]

instance Conjunction t (Conjunctions t) where
  (/\) e1 (Conjunction e2) = Conjunction (e1:e2)

newtype Graph t = Graph (NodeMap (Term t), Gr (t, Point (LNode t)) Int)
newtype Vert  t = Vert  (LNode (t, Point (LNode t)))

interleave :: [(a,a)] -> [a]
interleave ((x,y):rest) = x : y : interleave rest
interleave []           = []

termGraph :: (Monad m, Ord t) => [Equation t] -> UnionFindT (LNode t) m (Graph t)
termGraph = termGraph' . interleave . terms

termGraph' :: (Monad m, Ord t) => [Term t] -> UnionFindT (LNode t) m (Graph t)
termGraph' ts = do
  let (nodeMap, gr) = snd $ run empty $ traverse_ insertTerm ts
  vars <- traverse genVars (labNodes gr)
  return $ Graph (nodeMap, mkGraph vars (labEdges gr))
  where
    insertTerm :: Ord t => Term t -> NodeMapM (Term t) Int Gr ()
    insertTerm trm@(Function _ childs) = do
      _ <- insMapNodeM trm
      forM_ (zip childs [1..]) $ \(child,i) -> do
        _ <- insMapNodeM child
        insMapEdgeM (trm,child,i)
        insertTerm child

    genVars (node, Function name _) = do
      var <- fresh (node,name)
      return (node,(name,var))

vertex :: Ord t => Graph t -> Term t -> Vert t
vertex gr@(Graph (nodeMap,_)) trm =
  let (node,_) = mkNode_ nodeMap trm
  in label gr node

graph :: Graph t -> Gr (t, Point (LNode t)) Int
graph (Graph (_, gr)) = gr

vertices :: Graph t -> [Vert t]
vertices = map Vert . labNodes . graph

outDegree :: Graph t -> Vert t -> Int
outDegree (graph -> gr) (Vert (x, _)) = outdeg gr x

label :: Graph t -> Node -> Vert t
label (graph -> gr) a = Vert (a, fromJust (lab gr a))

equivalent :: (Monad m) => Vert t -> Vert t -> UnionFindT (LNode t) m Bool
equivalent (Vert (_,(_,x))) (Vert (_,(_,y))) = U.equivalent x y

union :: (Monad m) => Vert t -> Vert t -> UnionFindT (LNode t) m ()
union (Vert (_,(_,x))) (Vert (_,(_,y))) = U.union x y

predecessors :: Graph t -> Vert t -> [Vert t]
predecessors gr (Vert (x,_)) = label gr <$> pre (graph gr) x

successors :: Graph t -> Vert t -> [Vert t]
successors gr (Vert (x,_)) = label gr <$> suc (graph gr) x

terms :: [Equation t] -> [(Term t, Term t)]
terms = map go
  where
    go e = case e of
      Equal    t1 t2 -> (t1,t2)
      NotEqual t1 t2 -> (t1,t2)

term :: Graph t -> Vert t -> Term t
term (Graph (_,gr0)) (Vert (n0,_)) = go gr0 n0
  where
    go :: Gr (t, a) Int -> Node -> Term t
    go gr n =
      case match n gr of
        (Nothing,_) -> error "context is Nothing"
        (Just (_,_,(sym,_),out0),gr') ->
          Function sym $ map (go gr') $ sortEdges out0
    sortEdges out0 = map snd $ L.sortOn fst out0

partition :: Ord t => Graph t -> (Equation t -> Bool) -> [Equation t] -> ([(Vert t,Vert t)],[(Vert t,Vert t)])
partition gr f equations =
  let (as,bs) = L.partition f equations
  in (map (vertex gr *** vertex gr) $ terms as, map (vertex gr *** vertex gr) $ terms bs)

unless :: Monad m => m Bool -> m () -> m ()
unless mbool m = do
  b <- mbool
  Control.Monad.unless b m

instance Show t => Show (Vert t) where
  show (Vert (n, _)) = show n

positive :: Equation t -> Bool
positive t =
  case t of
    Equal _ _    -> True
    NotEqual _ _ -> False

any :: Monad m => (a -> b -> m Bool) -> [(a,b)] -> m Bool
any _ [] = return False
any f ((a,b):abs) = do
  r <- f a b
  if r
    then return True
    else any f abs


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
