{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitForAll        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImpredicativeTypes    #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.Program where

import           Control.DeepSeq
import           Data.Map.Strict    as Map
import           Language.Common    as C
import           Language.Instance  as I
import           Language.Mapping   as M
import           Language.Query     as Q
import           Language.Schema    as S
import           Language.Term      as Term
import           Language.Transform as Tr
import           Language.Typeside  as T
import           Prelude            hiding (EQ)

-- | Top level AQL expressions, untyped.
data Exp
  = ExpTy TypesideExp
  | ExpS  SchemaExp
  | ExpI  InstanceExp
  | ExpM  MappingExp
  | ExpT  TransformExp
  | ExpQ  QueryExp

-- | Top level AQL expressions, dynamically typed.
data Val
  = ValTy TypesideEx
  | ValS  SchemaEx
  | ValI  InstanceEx
  | ValM  MappingEx
  | ValT  TransformEx
  | ValQ  QueryEx
  deriving Show

instance NFData Val where
  rnf v = case v of
    ValTy x -> rnf x
    ValS  x -> rnf x
    ValI  x -> rnf x
    ValM  x -> rnf x
    ValT  x -> rnf x
    ValQ  x -> rnf x

-- | Equivalent to Ctx (String + ... + String) (ts + ... + t)
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

-- | AQL programs
type Prog  = KindCtx TypesideExp SchemaExp InstanceExp MappingExp QueryExp TransformExp [(String, String)]

newProg :: KindCtx ts s i m q t [a]
newProg = newEnv []

-- | The result of an AQL type checking pass.
type Types = KindCtx TypesideExp TypesideExp SchemaExp (SchemaExp,SchemaExp) (SchemaExp,SchemaExp) (InstanceExp,InstanceExp) ()

newTypes :: KindCtx ts s i m q t ()
newTypes = newEnv ()

newEnv :: o -> KindCtx ts s i m q t o
newEnv o = KindCtx m m m m m m o
  where m = Map.empty

instance TyMap Show '[ts, s, i, m, q, t, o] => Show (KindCtx ts s i m q t o) where
  show (KindCtx ts s i m q t o) =
    "typesides\n"  ++ showCtx'' ts ++ "\n" ++
    "schemas\n"    ++ showCtx'' s  ++ "\n" ++
    "instances\n"  ++ showCtx'' i  ++ "\n" ++
    "mappings\n"   ++ showCtx'' m  ++ "\n" ++
    "queries\n"    ++ showCtx'' q  ++ "\n" ++
    "transforms\n" ++ showCtx'' t  ++ "\n" ++
    "other\n"      ++ show o       ++ "\n"

allVars :: KindCtx ts s i m q t o -> [(String, Kind)]
allVars x =
  (fmap (\x'->(x', TYPESIDE )) $ keys $ typesides  x) ++
  (fmap (\x'->(x', SCHEMA   )) $ keys $ schemas    x) ++
  (fmap (\x'->(x', INSTANCE )) $ keys $ instances  x) ++
  (fmap (\x'->(x', MAPPING  )) $ keys $ mappings   x) ++
  (fmap (\x'->(x', QUERY    )) $ keys $ queries    x) ++
  (fmap (\x'->(x', TRANSFORM)) $ keys $ transforms x)

