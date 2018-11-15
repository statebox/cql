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
import           Language.Options
import           Control.DeepSeq

data Exp
 = ExpTy TypesideExp
 | ExpS SchemaExp
 | ExpI InstanceExp
 | ExpM MappingExp
 | ExpT TransformExp
 | ExpQ QueryExp

data Val
 = ValTy TypesideEx
 | ValS SchemaEx
 | ValI InstanceEx
 | ValM MappingEx
 | ValT TransformEx
 | ValQ QueryEx
  deriving Show

instance NFData Val where
  rnf v = case v of
      ValTy x -> rnf x
      ValS  x -> rnf x
      ValI  x -> rnf x
      ValM  x -> rnf x
      ValT  x -> rnf x
      ValQ  x -> rnf x

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

allVars :: KindCtx ts s i m q t o -> [(String, Kind)]
allVars x =
  (fmap (\x'->(x', TYPESIDE)) $ keys $ typesides  x) ++
  (fmap (\x'->(x', SCHEMA  )) $ keys $ schemas    x) ++
  (fmap (\x'->(x', INSTANCE)) $ keys $ instances  x) ++
  (fmap (\x'->(x', MAPPING )) $ keys $ mappings   x) ++
  (fmap (\x'->(x', QUERY   )) $ keys $ queries    x) ++
  (fmap (\x'->(x',TRANSFORM)) $ keys $ transforms x)

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

type Prog = KindCtx TypesideExp SchemaExp InstanceExp MappingExp QueryExp TransformExp [(String, String)]

type Types = KindCtx TypesideExp TypesideExp SchemaExp (SchemaExp,SchemaExp) (SchemaExp,SchemaExp) (InstanceExp,InstanceExp) ()

newProg :: KindCtx ts s i m q t [a]
newProg = KindCtx m m m m m m []
  where m = Map.empty

newTypes :: KindCtx ts s i m q t ()
newTypes = KindCtx m m m m m m ()
  where m = Map.empty

newEnv :: Options -> KindCtx ts s i m q t Options
newEnv o = KindCtx m m m m m m o
  where m = Map.empty
