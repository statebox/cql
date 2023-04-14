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
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitForAll        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImpredicativeTypes    #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE DerivingStrategies #-}

module Language.CQL.Common where

import           Control.Arrow   (left)
import           Data.Char
import           Data.Foldable   as Foldable (toList)
import           Data.Kind
import           Data.Map.Strict as Map hiding (foldl)
import           Data.Maybe
import           Data.Set        as Set (Set, empty, insert, member, singleton)
import           Data.Typeable

split' :: [(a, Either b1 b2)] -> ([(a, b1)], [(a, b2)])
split' []           = ([],[])
split' ((w, ei):tl) =
  let (a,b) = split' tl
  in case ei of
    Left  x -> ((w,x):a, b      )
    Right x -> (      a, (w,x):b)

fromListAccum :: (Ord v, Ord k) => [(k, v)] -> Map k (Set v)
fromListAccum []          = Map.empty
fromListAccum ((k,v):kvs) = Map.insert k op (fromListAccum kvs)
  where
    op = maybe (Set.singleton v) (Set.insert v) (Map.lookup k r)
    r  = fromListAccum kvs

-- | Converts a 'List' to a 'Set', returning an error when there are duplicate bindings.
toSetSafely :: (Show k, Ord k) => [k] -> Err (Set k)
toSetSafely [] = return Set.empty
toSetSafely (k:l) = do
  l' <- toSetSafely l
  if Set.member k l'
  then Left $ "Duplicate binding: " ++ show k
  else pure $ Set.insert k l'

-- | Converts an association list to a 'Map', returning an error when there are duplicate bindings.
toMapSafely :: (Show k, Ord k) => [(k,v)] -> Err (Map k v)
toMapSafely [] = return Map.empty
toMapSafely ((k,v):l) = do
  l' <- toMapSafely l
  if Map.member k l'
  then Left $ "Duplicate binding: " ++ show k
  else pure $ Map.insert k v l'

lookup' :: (Show k, Show a, Ord k) => k -> Map k a -> a
lookup' m v = fromMaybe (error $ "Can't find " ++ show v ++ " in " ++ show m) $ Map.lookup m v

wrapError :: String -> Either String b -> Either String b
wrapError prefix se = (\s -> prefix ++ ": " ++ s) `left` se

class Deps a where
  deps :: a -> [(String, Kind)]

type a + b = Either a b

type Err = Either String

-- generic helper inspired by https://pursuit.purescript.org/search?q=note
note :: b -> Maybe a -> Either b a
note n = maybe (Left n) Right

data Kind = CONSTRAINTS | TYPESIDE | SCHEMA | INSTANCE | MAPPING | TRANSFORM | QUERY | COMMAND | GRAPH | COMMENT | SCHEMA_COLIMIT
  deriving stock (Show, Eq, Ord)

type ID = Integer

-- | Drop quotes if argument doesn't contain a space.
dropQuotes :: String -> String
dropQuotes s = if ' ' `elem` s then Prelude.filter (not . ('\"' ==)) s
                               else s

section :: String -> String -> String
section heading body = heading ++ "\n" ++ indentLines body

indentLines :: String -> String
indentLines = foldMap (\l -> tab <> l <> "\n"). lines

tab :: String
tab = "    "

sepTup :: (Show a1, Show a2) => String -> (a1, a2) -> String
sepTup sep (k,v) = show k ++ sep ++ show v

-- | A version of intercalate that works on Foldables instead of just List,
-- | adapted from PureScript.
intercalate :: (Foldable f, Monoid m) => m -> f m -> m
intercalate sep xs = snd (foldl go (True, mempty) xs)
  where
    go (True, _)   x = (False, x)
    go (_   , acc) x = (False, acc <> sep <> x)

mapl :: Foldable f => (a -> b) -> f a -> [b]
mapl fn = fmap fn . Foldable.toList

-- | Converts a String to lowercase, like Data.List.Extra.lower.
lower :: String -> String
lower = fmap toLower

-- | Heterogenous membership in a list
elem' :: (Typeable t, Typeable a, Eq a) => t -> [a] -> Bool
elem' x ys = maybe False (`elem` ys) (cast x)

-- | Heterogenous membership in the keys of a map list
member' :: (Typeable t, Typeable a, Eq a) => t -> Map a v -> Bool
member' k m = elem' k (Map.keys m)

mergeMaps :: Ord k => [Map k v] -> Map k v
mergeMaps = foldl Map.union Map.empty

-- | Allows to set a constraint for multiple type variables at the same time.
-- For example you could use `TyMap Show '[a, b, c]` instead of
-- `(Show a, Show b, Show c)`
-- The drawback of using this is that the compiler will treat this as a unique
-- constraint, so it won't be able to detect specific unused constraints
type family TyMap (f :: Type -> Constraint) (xs :: [Type]) :: Constraint
type instance TyMap f '[] = ()
type instance TyMap f (t ': ts) = (f t, TyMap f ts)

-- | Allows to set multiple contraints for multiple type variables at the same
-- time.
-- For example you could use `MultiTyMap '[Show, Ord] '[a, b, c]` insted of
-- `(Show a, Ord a, Show b, Ord b, Show c, Ord c)`
-- The drawback of using this is that the compiler will treat this as a unique
-- constraint, so it won't be able to detect specific unused constraints
type family MultiTyMap (fs :: [Type -> Constraint]) (xs :: [Type]) :: Constraint
type instance MultiTyMap '[] _ = ()
type instance MultiTyMap (f : fs) xs = (TyMap f xs, MultiTyMap fs xs)
