{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Instance where
import Prelude hiding (EQ)
import Data.Set as Set
import Data.Map.Strict as Map
import Language.Common
import Language.Term
import Language.Schema
import Language.Mapping
import Language.Query
import Data.Void

--------------------------------------------------------------------------------

data Algebra var ty sym en fk att gen sk x y
  = Algebra
  { schemaA :: Schema var ty sym en fk att

  , ens     :: Map en (Set x)
  , fks     :: Map fk (Map x x)
  , atts    :: Map att (Map x (Term Void ty sym Void Void Void Void y))

  , nf      :: Term Void Void Void en fk Void gen Void -> x
  , repr    :: x -> Term Void Void Void en fk Void gen Void

  , nf'     :: Term var ty sym en fk att gen sk ->
               Term Void ty sym Void Void Void Void y

  , repr'   :: Term Void ty sym Void Void Void Void y ->
               Term var ty sym en fk att gen sk
  } -- omit Eq, doesn't seem to be necessary for now

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y)
  => Show (Algebra var ty sym en fk att gen sk x y) where
  show (Algebra _ ens' fks' atts' _ _ _ _) =
    "ens = " ++ show ens' ++
    "\nfks = " ++ show fks' ++ "\natts = " ++ show atts'

data Instance var ty sym en fk att gen sk x y
  = Instance
  { ischema  :: Schema var ty sym en fk att
  , igens    :: Map gen en
  , isks     :: Map sk ty
  , ieqs     :: Set (EQ Void ty sym en fk att gen sk)
  , ieq      :: EQ Void ty sym en fk att gen sk -> Bool

  , algebra :: Algebra var ty sym en fk att gen sk x y
  }

data InstanceEx :: * where
  InstanceEx :: forall var ty sym en fk att gen sk x y. Instance var ty sym en fk att gen sk x y -> InstanceEx


instToCol :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk)
   => Instance var ty sym en fk att gen sk x y -> Collage (()+var) ty sym en fk att gen sk
instToCol (Instance sch gens sks eqs _ _) =
 Collage (Set.union e1 e2) (ctys schcol)
  (cens schcol) (csyms schcol) (cfks schcol) (catts schcol) gens sks
   where schcol = schToCol sch
         e1 = Set.map (\(EQ (l,r)) -> (Map.empty, EQ (up4 l, up4 r))) eqs
         e2 = Set.map (\(g, EQ (l,r))->(g, EQ (up5 l, up5 r))) $ ceqs schcol

up4 :: Term Void ty sym en fk att gen sk -> Term x ty sym en fk att gen sk
up4 (Var v) = absurd v
up4 (Sym f x) = Sym f $ Prelude.map up4 x
up4 (Fk f a) = Fk f $ up4 a
up4 (Att f a) = Att f $ up4 a
up4 (Gen f) = Gen f
up4 (Sk f) = Sk f

up5 :: Term var ty sym en fk att Void Void -> Term var ty sym en fk att gen sk
up5 (Var v) = Var v
up5 (Sym f x) = Sym f $ Prelude.map up5 x
up5 (Fk f a) = Fk f $ up5 a
up5 (Att f a) = Att f $ up5 a
up5 (Gen f) = absurd f
up5 (Sk f) = absurd f

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y)
  => Show (Instance var ty sym en fk att gen sk x y) where
  show (Instance _ gens sks eqs _ _) =
    "gens = " ++ show gens ++
    "\nsks = " ++ show sks ++ "\neqs = " ++ show eqs

-- in java we just use pointer equality.  this is better, but really
-- we want that the intances denote the same set-valued functor,
-- possibly up to natural isomorphism. in practice equality only
-- happens during type checking, so the check below suffices... but
-- hopefully it won't incur a performance penalty.  side note:
-- eventually schema equality will need to be relaxed too.
instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Eq x, Eq y)
  => Eq (Instance var ty sym en fk att gen sk x y) where
  (==) (Instance schema gens sks eqs _ _) (Instance schema' gens' sks' eqs' _ _)
    = (schema == schema') && (gens == gens') && (sks == sks') && (eqs == eqs')

--instance Semantics (Instance var ty sym en fk att gen sk x y)  where
 -- validate = undefined

-- adds one equation per fact in the algebra.
algebraToInstance
  :: Algebra var ty sym en fk att gen sk x y
  -> Instance var ty sym en fk att gen sk x y
algebraToInstance _ = undefined

--------------------------------------------------------------------------------


data InstanceExp where
  InstanceVar :: String -> InstanceExp
  InstanceInitial :: SchemaExp -> InstanceExp

  InstanceDelta :: MappingExp -> InstanceExp -> InstanceExp
  InstanceSigma :: MappingExp -> InstanceExp -> InstanceExp
  InstancePi :: MappingExp -> InstanceExp -> InstanceExp

  InstanceEval :: QueryExp -> InstanceExp -> InstanceExp
  InstanceCoEval :: MappingExp -> InstanceExp -> InstanceExp

  InstanceRaw :: InstExpRaw' -> InstanceExp

data InstExpRaw' = InstExpRaw' {
    instraw_gens  :: [(String, String)]
  , instraw_sks :: [(String, String)]
  , instraw_oeqs  :: [(RawTerm, RawTerm)]
  , instraw_options :: [(String, String)]
} deriving (Eq, Show)

evalDeltaAlgebra
  :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y, Eq en', Eq fk', Eq att')
  => Mapping  var ty sym en  fk  att  en'       fk' att'
  -> Instance var ty sym en' fk' att' gen       sk  x       y
  -> Algebra  var ty sym en  fk  att  (en',gen) sk  (en',x) y
evalDeltaAlgebra = undefined --todo

evalDeltaInst
  :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y, Eq en', Eq fk', Eq att')
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en' fk' att' gen sk x y
  -> Instance var ty sym en fk att (en',gen) sk (en',x) y
evalDeltaInst = undefined --todo

-- TODO all of these need to be changed at once
--data ErrEval = ErrSchemaMismatch | ErrQueryEvalTodo | ErrMappingEvalTodo | ErrInstanceEvalTodo


