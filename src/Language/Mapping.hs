{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Mapping where
import Prelude hiding (EQ)
import Data.Map.Strict as Map
import Language.Term
import Language.Schema
import Data.Void

--------------------------------------------------------------------------------

data Mapping var ty sym en fk att en' fk' att'
  = Mapping
  { src  :: Schema var ty sym en  fk  att
  , dst  :: Schema var ty sym en' fk' att'

  , ens  :: Map en  en'
  , fks  :: Map fk  (Term () Void Void en' fk' Void Void Void)
  , atts :: Map att (Term () ty   sym  en' fk' att' Void Void)
  }

data MappingEx :: * where
  MappingEx :: forall var ty sym en fk att en' fk' att'. 
   (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att') =>  
    Mapping var ty sym en fk att en' fk' att' -> MappingEx

deriving instance Show MappingEx  

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att')
  => Show (Mapping var ty sym en fk att en' fk' att') where
  show (Mapping _ _ ens' fks' atts') =
    "ens = " ++ (show ens') ++
    "\nfks = " ++ (show fks') ++ "\natts = " ++ (show atts')

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq en', Eq fk', Eq att')
  => Eq (Mapping var ty sym en fk att en' fk' att') where
  (Mapping s1' s2' ens' fks' atts') == (Mapping s1'' s2'' ens'' fks'' atts'')
    = (s1' == s1'') && (s2' == s2'') && (ens' == ens'') && (fks' == fks'') && (atts' == atts'')

validateMapping :: Mapping var ty sym en fk att en' fk' att' -> Maybe String
validateMapping = undefined


data MappingExp   where
  MappingVar     :: String -> MappingExp
  MappingId      :: SchemaExp -> MappingExp
  MappingRaw     :: MapExpRaw' -> MappingExp
 deriving Show

data MapExpRaw' = MapExpRaw' {
    mapraw_ens  :: [(String, String)]
  , mapraw_fks :: [(String, [String])]
  , mapraw_atts  :: [(String, (String, String, RawTerm))]
  , mapraw_options :: [(String, String)]
} deriving (Eq, Show)




-- the type of the collage isn't quite right here
--instance Semantics (Mapping var ty sym en fk att en' fk' att')  where
--  validate = undefined
