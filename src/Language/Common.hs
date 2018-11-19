{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies, ConstraintKinds, TypeFamilies, DataKinds #-}

module Language.Common where
import Data.Map.Strict as Map hiding (foldl)
import Data.Foldable as Foldable (foldl, toList)
import Data.Kind
import Data.Typeable
import Control.DeepSeq
import Control.Arrow (left)
import Data.Maybe
import Data.Set as Set (Set, empty, member, insert)
import Data.Char

showCtx :: (Show a1, Show a2) => Map a1 a2 -> [Char]
showCtx m = intercalate " " $ Prelude.map (\(k,v) -> show k ++ " : " ++ show v) $ Map.toList m

fromList'' :: (Show k, Ord k) => [k] -> Err (Set k)
fromList'' [] = return Set.empty
fromList'' (k:l) = do
  l' <- fromList'' l
  if Set.member k l'
  then Left $ "Duplicate binding: " ++ (show k)
  else pure $ Set.insert k l'

fromList' :: (Show k, Ord k) => [(k,v)] -> Err (Map k v)
fromList' [] = return Map.empty
fromList' ((k,v):l) = do
  l' <- fromList' l
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

toMapSafely :: (Ord k, Show k) => [(k, a)] -> Either [Char] (Map k a)
toMapSafely [] = return $ Map.empty
toMapSafely ((k,v):x) = do
  y <- toMapSafely x
  if Map.member k y
  then Left $ "Duplicate element " ++ (show k)
  else return $ Map.insert k v y

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

elem' :: (Typeable t, Typeable a, Eq a) => t -> [a] -> Bool
elem' x ys = maybe False (flip elem ys) (cast x)

member' :: (Typeable t, Typeable a, Eq a) => t -> Map a v -> Bool
member' k m = elem' k (Map.keys m)

mergeMaps :: Ord k => [Map k v] -> Map k v
mergeMaps []    = Map.empty
mergeMaps (x:y) = Map.union x $ mergeMaps y

-- I'd like to write 'TyMap f `[a,b,c]' instead of (f a, f b, f c) in instance declarations etc
-- but it doesn't quite work.
type family TyMap (f :: * -> Constraint) (xs :: [*]) :: Constraint
type instance TyMap f '[] = ()
type instance TyMap f (t ': ts) = (f t, TyMap f ts)

type family ShowOrdN (xs :: [*]) :: Constraint
type instance ShowOrdN '[] = ()
type instance ShowOrdN (t ': ts) = (Show t, Ord t, NFData t, ShowOrdN ts)

type family ShowOrdTypeableN (xs :: [*]) :: Constraint
type instance ShowOrdTypeableN '[] = ()
type instance ShowOrdTypeableN (t ': ts) = (Show t, Ord t, Typeable t, NFData t, ShowOrdTypeableN ts)
