{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies, ConstraintKinds, TypeFamilies, DataKinds #-}

module Language.Common where
import Data.Map.Strict as Map hiding (foldl, toList)
import Data.Foldable (foldl, toList)
import Data.Kind
import Data.Typeable

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
toMapSafely ((k,v):x) =
    do y <- toMapSafely x
       if Map.member k y
       then Left $ "Duplicate element " ++ (show k)
       else return $ Map.insert k v y


lookup2 :: Ord k => k -> Map k a -> a
lookup2 m x = case Map.lookup m x of
  Just y -> y
  Nothing -> undefined

-- | A version of intercalate that works on Foldables instead of just List,
-- | adapted from PureScript.
intercalate :: (Foldable f, Monoid m) => m -> f m -> m
intercalate sep xs = snd (foldl go (True, mempty) xs)
  where
    go (True, _)   x = (False, x)
    go (_   , acc) x = (False, acc <> sep <> x)

mapl :: Foldable f => (a -> b) -> f a -> [b]
mapl fn = fmap fn . toList

type family ShowOrdN (xs :: [*]) :: Constraint
type instance ShowOrdN '[] = ()
type instance ShowOrdN (t ': ts) = (Show t, Ord t, ShowOrdN ts)

type family ShowOrdTypeableN (xs :: [*]) :: Constraint
type instance ShowOrdTypeableN '[] = ()
type instance ShowOrdTypeableN (t ': ts) = (Show t, Ord t, Typeable t, ShowOrdTypeableN ts)
