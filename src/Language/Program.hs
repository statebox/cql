
{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Program where

import Prelude hiding (EQ)
import Data.Map.Strict as Map
import Language.Common as C
import Language.Term as Term
import Language.Schema as S
import Language.Instance as I
import Language.Mapping as M
import Language.Typeside as T
import Language.Transform as Tr
import Language.Query as Q


data Exp =
   ExpTy (TypesideExp)
 | ExpS (SchemaExp)
 | ExpI (InstanceExp)
 | ExpM (MappingExp)
 | ExpT (TransformExp)
 | ExpQ (QueryExp)

data KindCtx ts s i m q t o = KindCtx {
    typesides :: Ctx String ts
  , schemas :: Ctx String s
  , instances :: Ctx String i
  , mappings :: Ctx String m
  , queries :: Ctx String q
  , transforms :: Ctx String t
  , other :: o
}

instance (Show ts, Show s, Show i, Show m, Show q, Show t, Show o) => Show (KindCtx ts s i m q t o) where
     show (KindCtx ts s i m q t o) =
        "typesides\n" ++ showCtx'' ts ++
        "\nschemas\n" ++ showCtx'' s ++
        "\ninstances\n" ++ showCtx'' i ++
        "\nmappings\n" ++ showCtx'' m ++
        "\nqueries\n" ++ showCtx'' q ++
        "\ntransforms\n" ++ showCtx'' t ++
        "\nother\n" ++ show o ++ "\n"

showCtx'' :: (Show a1, Show a2) => Map a1 a2 -> [Char]
showCtx'' m = intercalate "\n" $ Prelude.map (\(k,v) -> show k ++ " = " ++ show v ++ "\n") $ Map.toList m

lookup' :: (Show k, Show a, Ord k) => k -> Map k a -> a
lookup' m v = f $ Map.lookup m v
  where
    f (Just x) = x
    f Nothing  = error $ "Can't find " ++ show v ++ " in " ++ show m

--todo: store line numbers in other field
type Prog = KindCtx TypesideExp SchemaExp InstanceExp MappingExp QueryExp TransformExp ([(String,Kind)])

type Types = KindCtx TypesideExp TypesideExp SchemaExp (SchemaExp,SchemaExp) (SchemaExp,SchemaExp) (InstanceExp,InstanceExp) ()

newProg :: KindCtx ts s i m q t [a]
newProg = KindCtx m m m m m m []
 where m = Map.empty

newTypes :: KindCtx ts s i m q t ()
newTypes = KindCtx m m m m m m ()
 where m = Map.empty


newEnv :: KindCtx ts s i m q t ()
newEnv = KindCtx m m m m m m ()
 where m = Map.empty
