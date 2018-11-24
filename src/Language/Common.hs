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

module Language.Common where

import           Control.Arrow   (left)
import           Data.Char
import           Data.Foldable   as Foldable (foldl, toList)
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

showCtx :: (Show a1, Show a2) => Map a1 a2 -> [Char]
showCtx m = intercalate " " $ Prelude.map (\(k,v) -> show k ++ " : " ++ show v) $ Map.toList m

fromList'' :: (Show k, Ord k) => [k] -> Err (Set k)
fromList'' [] = return Set.empty
fromList'' (k:l) = do
  l' <- fromList'' l
  if Set.member k l'
  then Left $ "Duplicate binding: " ++ (show k)
  else pure $ Set.insert k l'

-- | Converts a map to a finite list, returning an error when there are duplicate bindings.
toMapSafely :: (Show k, Ord k) => [(k,v)] -> Err (Map k v)
toMapSafely [] = return Map.empty
toMapSafely ((k,v):l) = do
  l' <- toMapSafely l
  if Map.member k l'
  then Left $ "Duplicate binding: " ++ (show k)
  else pure $ Map.insert k v l'

showCtx'' :: (Show a1, Show a2) => Map a1 a2 -> String
showCtx'' m = intercalate "\n" $ (\(k,v) -> show k ++ " = " ++ show v ++ "\n") <$> Map.toList m

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
note n x = maybe (Left n) Right x

data Kind = CONSTRAINTS | TYPESIDE | SCHEMA | INSTANCE | MAPPING | TRANSFORM | QUERY | COMMAND | GRAPH | COMMENT | SCHEMA_COLIMIT
 deriving (Show, Eq, Ord)

type ID = Integer


showCtx' :: (Show a1, Show a2) => Map a1 a2 -> [Char]
showCtx' m = intercalate "\n\t" $ fmap (\(k,v) -> show k ++ " : " ++ show v) $ Map.toList m

-- | A version of intercalate that works on Foldables instead of just List,
-- | adapted from PureScript.
intercalate :: (Foldable f, Monoid m) => m -> f m -> m
intercalate sep xs = snd (foldl go (True, mempty) xs)
  where
    go (True, _)   x = (False, x)
    go (_   , acc) x = (False, acc <> sep <> x)

mapl :: Foldable f => (a -> b) -> f a -> [b]
mapl fn = fmap fn . Foldable.toList

toLowercase :: String -> String
toLowercase = Prelude.map toLower

-- | Heterogenous membership in a list
elem' :: (Typeable t, Typeable a, Eq a) => t -> [a] -> Bool
elem' x ys = maybe False (flip elem ys) (cast x)

-- | Heterogenous membership in the keys of a map list
member' :: (Typeable t, Typeable a, Eq a) => t -> Map a v -> Bool
member' k m = elem' k (Map.keys m)

mergeMaps :: Ord k => [Map k v] -> Map k v
mergeMaps = foldl Map.union Map.empty

type family TyMap (f :: * -> Constraint) (xs :: [*]) :: Constraint
type instance TyMap f '[] = ()
type instance TyMap f (t ': ts) = (f t, TyMap f ts)

type family MultiTyMap (fs :: [* -> Constraint]) (xs :: [*]) :: Constraint
type instance MultiTyMap '[] _ = ()
type instance MultiTyMap (f : fs) xs = (TyMap f xs, MultiTyMap fs xs)
