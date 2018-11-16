{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Query where
import Prelude hiding (EQ)
import Data.Set as Set
import Data.Map.Strict as Map
import Language.Term
import Data.Void
import Language.Schema
import Language.Common
import Control.DeepSeq

data Query var ty sym en fk att en' fk' att'
  = Query
  { srcQ :: Schema var ty sym en fk att
  , dstQ :: Schema var ty sym en' fk' att'

  , ens  :: Map en' (Ctx var en, Set (EQ var ty sym en fk att Void Void))
  , fks  :: Map fk'  (Ctx var (Term var Void Void en fk Void Void Void))
  , atts :: Map att' (Term var ty   sym  en fk att  Void Void)
  }

instance NFData QueryEx where
  rnf (QueryEx _) = undefined

data QueryEx :: * where
  QueryEx :: forall var ty sym en fk att en' fk' att'.
   (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att') =>
    Query var ty sym en fk att en' fk' att' -> QueryEx

deriving instance Show QueryEx

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att')
  => Show (Query var ty sym en fk att en' fk' att') where
  show (Query _ _ ens' fks' atts') =
    "ens = " ++ show ens' ++
    "\nfks = " ++ show fks' ++ "\natts = " ++ show atts'

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq en', Eq fk', Eq att')
  => Eq (Query var ty sym en fk att en' fk' att') where
  (==) (Query s1' s2' ens' fks' atts') (Query s1'' s2'' ens'' fks'' atts'')
    = (s1' == s1'') && (s2' == s2'') && (ens' == ens'') && (fks' == fks'') && (atts' == atts'')



data QueryExp where
  QueryVar     :: String -> QueryExp
  QueryId      :: SchemaExp -> QueryExp
  QueryRaw     :: QueryExpRaw' -> QueryExp
 deriving (Eq,Show)

instance Deps QueryExp where
 deps (QueryVar v) = [(v, QUERY)]
 deps (QueryId s) = deps s
 deps (QueryRaw (QueryExpRaw' _ _ _ _)) = error "todo - queries"


--old school queries without overlapping names across entities
data QueryExpRaw' = QueryExpRaw' {
    qraw_ens  :: [(String, ([(String,String)],[(RawTerm,RawTerm)]))]
  , qraw_fks :: [(String, [(String,RawTerm)])]
  , qraw_atts  :: [(String, RawTerm)]
  , qraw_options :: [(String, String)]
} deriving (Eq, Show)

--instance Semantics (Query var ty sym en fk att en' fk' att')  where
--  validate = undefined

--------------------------------------------------------------------------------
