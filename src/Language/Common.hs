{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Common where 
import Data.Map.Strict as Map

type a + b = Either a b   

type Err = Either String

-- generic helper inspired by https://pursuit.purescript.org/search?q=note
note :: b -> Maybe a -> Either b a
note n x = maybe (Left n) Right x 

data Kind = CONSTRAINTS | TYPESIDE | SCHEMA | INSTANCE | MAPPING | TRANSFORM | QUERY | COMMAND | GRAPH | COMMENT | SCHEMA_COLIMIT
 deriving Show
 
type ID = Integer

toMapSafely [] = return $ Map.empty
toMapSafely ((k,v):x) = 
    do y <- toMapSafely x
       if Map.member k y 
       then Left $ "Duplicate element " ++ (show k)
       else return $ Map.insert k v y


lookup2 m x = case Map.lookup m x of Just y -> y
