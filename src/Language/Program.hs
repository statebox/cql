{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs
           , KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances
           , MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators, LiberalTypeSynonyms, ImpredicativeTypes
           , UndecidableInstances, FunctionalDependencies
#-}

module Language.Program where

import           Prelude hiding (EQ)
import           Data.Maybe (fromMaybe)
import           Data.Map.Strict as Map
import           Language.Common as C
import           Language.Instance as I
import           Language.Mapping as M
import           Language.Schema as S
import           Language.Term as Term
import           Language.Query as Q
import           Language.Transform as Tr
import           Language.Typeside as T

data Exp
 = ExpTy TypesideExp
 | ExpS SchemaExp
 | ExpI InstanceExp
 | ExpM MappingExp
 | ExpT TransformExp
 | ExpQ QueryExp

data KindCtx ts s i m q t o
  = KindCtx
  { typesides  :: Ctx String ts
  , schemas    :: Ctx String s
  , instances  :: Ctx String i
  , mappings   :: Ctx String m
  , queries    :: Ctx String q
  , transforms :: Ctx String t
  , other      :: o
  }

instance (Show ts, Show s, Show i, Show m, Show q, Show t, Show o) => Show (KindCtx ts s i m q t o) where
  show (KindCtx ts s i m q t o) =
    "typesides\n"  ++ showCtx'' ts ++ "\n" ++
    "schemas\n"    ++ showCtx'' s  ++ "\n" ++
    "instances\n"  ++ showCtx'' i  ++ "\n" ++
    "mappings\n"   ++ showCtx'' m  ++ "\n" ++
    "queries\n"    ++ showCtx'' q  ++ "\n" ++
    "transforms\n" ++ showCtx'' t  ++ "\n" ++
    "other\n"      ++ show o       ++ "\n"

showCtx'' :: (Show a1, Show a2) => Map a1 a2 -> String
showCtx'' m = intercalate "\n" $ (\(k,v) -> show k ++ " = " ++ show v ++ "\n") <$> Map.toList m

lookup' :: (Show k, Show a, Ord k) => k -> Map k a -> a
lookup' m v = fromMaybe (error $ "Can't find " ++ show v ++ " in " ++ show m) $ Map.lookup m v

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
