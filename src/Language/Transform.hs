{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Transform where
import Prelude hiding (EQ)
import Data.Map.Strict as Map
import Language.Term
import Language.Instance
import Language.Mapping
import Language.Query
import Data.Void

data Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  = Transform
  { srcT :: Instance var ty sym en fk att gen sk x y
  , dstT :: Instance var ty sym en fk att gen' sk' x' y'
  , gens :: Map gen (Term Void Void Void en fk Void gen' Void)
  , sks  :: Map sk  (Term var  ty   sym  en fk att  gen' sk')
  }

data TransformEx :: * where
  TransformEx :: forall var ty sym en fk att gen sk x y gen' sk' x' y' .
    Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> TransformEx

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk,
          Show x, Show y, Show gen', Show sk', Show x', Show y')
  => Show (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  show (Transform _ _ gens' sks') =
    "gens = " ++ (show gens') ++
    "\nsks = " ++ (show sks')

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Eq x, Eq y, Eq gen', Eq sk', Eq x', Eq y')
  => Eq (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  (==) (Transform s1' s2' gens' sks') (Transform s1'' s2'' gens'' sks'')
    = (s1' == s1'') && (s2' == s2'') && (gens' == gens'') && (sks' == sks'')


data TransformExp  where
  TransformVar :: String -> TransformExp
  TransformId :: InstanceExp -> TransformExp
  TransformSigmaDeltaUnit :: MappingExp -> TransformExp
  TransformSigmaDeltaCoUnit :: MappingExp -> TransformExp
  TransformDeltaPiUnit :: MappingExp -> TransformExp
  TransformDeltaPiCoUnit :: MappingExp -> TransformExp
  TransformQueryUnit :: QueryExp -> TransformExp
  TransformQueryCoUnit :: MappingExp -> TransformExp
  TransformDelta :: MappingExp -> TransformExp -> TransformExp
  TransformSigma :: MappingExp -> TransformExp -> TransformExp
  TransformPi :: MappingExp -> TransformExp -> TransformExp
  TransformCoEval :: QueryExp -> TransformExp -> TransformExp
  TransformEval :: QueryExp -> TransformExp -> TransformExp
  TransformRaw :: TransExpRaw' -> TransformExp

data TransExpRaw' = TransExpRaw' {
    transraw_gens  :: [(String, RawTerm)]
  , transraw_sks :: [(String, RawTerm)]
  , transraw_options :: [(String, String)]
} deriving (Eq, Show)


--instance Semantics (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
--  validate = undefined
