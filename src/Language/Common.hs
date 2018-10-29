{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies, ConstraintKinds #-}

module Language.Common where
import Data.Map.Strict as Map hiding (foldl, toList)
import Data.Foldable (foldl, toList)
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

type ShowOrd a = (Show a, Ord a)

type ShowOrd2 a b = (ShowOrd a, ShowOrd b)

type ShowOrd3 a b c = (ShowOrd2 a b, ShowOrd c)

type ShowOrd4 a b c d = (ShowOrd3 a b c, ShowOrd d)

type ShowOrd5 a b c d e = (ShowOrd4 a b c d, ShowOrd e)

type ShowOrd6 a b c d e f = (ShowOrd5 a b c d e, ShowOrd f)

type ShowOrd7 a b c d e f g = (ShowOrd6 a b c d e f, ShowOrd g)

type ShowOrd8 a b c d e f g h = (ShowOrd7 a b c d e f g, ShowOrd h)

type ShowOrd9 a b c d e f g h i = (ShowOrd8 a b c d e f g h, ShowOrd i)

type ShowOrd10 a b c d e f g h i j = (ShowOrd9 a b c d e f g h i, ShowOrd j)

type ShowOrd11 a b c d e f g h i j k = (ShowOrd10 a b c d e f g h i j, ShowOrd k)

type ShowOrd12 a b c d e f g h i j k l = (ShowOrd11 a b c d e f g h i j k, ShowOrd l)

type ShowOrd13 a b c d e f g h i j k l m = (ShowOrd12 a b c d e f g h i j k l, ShowOrd m)

type ShowOrdTypeable a = (Show a, Ord a, Typeable a)

type ShowOrdTypeable2 a b = (ShowOrdTypeable a, ShowOrdTypeable b)

type ShowOrdTypeable3 a b c = (ShowOrdTypeable2 a b, ShowOrdTypeable c)

type ShowOrdTypeable4 a b c d = (ShowOrdTypeable3 a b c, ShowOrdTypeable d)

type ShowOrdTypeable5 a b c d e = (ShowOrdTypeable4 a b c d, ShowOrdTypeable e)

type ShowOrdTypeable6 a b c d e f = (ShowOrdTypeable5 a b c d e, ShowOrdTypeable f)
