{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies, ScopedTypeVariables #-}

module Language.Instance where
import Prelude hiding (EQ)
import Data.Set as Set
import Data.Map.Strict as Map 
import Data.List
import Language.Common
import Language.Term as Term
import Language.Schema
import Language.Mapping
import Language.Query
import Data.Void

--------------------------------------------------------------------------------

data Algebra var ty sym en fk att gen sk x y
  = Algebra { 
   schema :: Schema var ty sym en fk att

  , en    :: en -> (Set x)
  , nf    :: Term Void Void Void en fk Void gen Void -> x
  , repr  :: x -> Term Void Void Void en fk Void gen Void

  , ty    :: ty -> (Set y)
  , nf'   :: sk + (x, att) -> Term Void ty sym Void Void Void Void y

  , repr' :: y -> Term Void ty sym en fk att gen sk
  , teqs  :: Set (EQ Void ty sym Void Void Void Void y)

  } -- omit Eq, doesn't seem to be necessary for now

nf'' :: Algebra var ty sym en fk att gen sk x y -> Term Void ty sym en fk att gen sk -> Term Void ty sym Void Void Void Void y 
nf'' alg (Sym f as) = Sym f $ Prelude.map (nf'' alg) as
nf'' alg (Att f a) = nf' alg $ Right (nf alg a, f) 

aGen :: Algebra var ty sym en fk att gen sk x y -> gen -> x
aGen alg g = nf alg $ Gen g

aFk :: Algebra var ty sym en fk att gen sk x y -> fk -> x -> x
aFk alg f x = nf alg $ Fk f $ repr alg x

aAtt :: Algebra var ty sym en fk att gen sk x y -> att -> x -> Term Void ty sym Void Void Void Void y 
aAtt alg f x = nf'' alg $ Att f $ repr alg x

aSk :: Algebra var ty sym en fk att gen sk x y -> sk -> Term Void ty sym Void Void Void Void y
aSk alg g = nf'' alg $ Sk g

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y)
  => Show (Algebra var ty sym en fk att gen sk x y) where
  show (Algebra sch en nf repr ty nf' repr' teqs) = undefined 


data Presentation var ty sym en fk att gen sk 
 = Presentation {
    gens    :: Map gen en
  , sks     :: Map sk ty
  , eqs     :: Set (EQ Void ty sym en fk att gen sk)
}


instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk)
  => Show (Presentation var ty sym en fk att gen sk) where
  show (Presentation ens fks eqs) =
    "gens = " ++ show ens ++
    "\nfks = " ++ show fks ++ "\neqs = " ++ show eqs


data Instance var ty sym en fk att gen sk x y
  = Instance { 
    schema  :: Schema var ty sym en fk att
  , pres    :: Presentation var ty sym en fk att gen sk
  , dp      :: EQ Void ty sym en fk att gen sk -> Bool
  , algebra :: Algebra var ty sym en fk att gen sk x y
  }

data InstanceEx :: * where
  InstanceEx :: forall var ty sym en fk att gen sk x y. Instance var ty sym en fk att gen sk x y -> InstanceEx


instToCol :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk)
   => Schema var ty sym en fk att -> Presentation var ty sym en fk att gen sk -> Collage (()+var) ty sym en fk att gen sk
instToCol sch (Presentation gens sks eqs) =
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
  show (Instance _ (Presentation gens sks eqs) _ _) =
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
  (==) (Instance schema (Presentation gens sks eqs) _ _) (Instance schema' (Presentation gens' sks' eqs') _ _)
    = (schema == schema') && (gens == gens') && (sks == sks') && (eqs == eqs')

--instance Semantics (Instance var ty sym en fk att gen sk x y)  where
 -- validate = undefined

-- adds one equation per fact in the algebra.
algebraToInstance
  :: Algebra var ty sym en fk att gen sk x y
  -> Instance var ty sym en fk att gen sk x y
algebraToInstance _ = undefined



lookup2 m x = case Map.lookup m x of Just y -> y 

-- simplification of talg will now be phrased as a fixpoint of algebra functions 

initialAlgebra :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk)
 => Presentation var ty sym en fk att gen sk -> (EQ (()+var) ty sym en fk att gen sk -> Bool) 
 -> Schema var ty sym en fk att ->
 Algebra var ty sym en fk att gen sk (GTerm en fk gen) (TTerm en fk att gen sk)
initialAlgebra p dp sch = this
 where this = Algebra sch en nf repr ty nf' repr' teqs
       col = instToCol sch p
       ens  = assembleGens col (close col dp)
       en k = lookup2 k ens
       nf e = let t = typeOf col e 
                  f [] = undefined -- impossible
                  f (a:b) = if dp (EQ (up a, up e)) then a else f b
              in f $ Set.toList $ lookup2 t ens 
       repr x = x
               
       tys = assembleSks col ens    
       ty y = lookup2 y tys    
       nf' (Left g) = Sk $ Left g
       nf' (Right (x, att)) = Sk $ Right (repr x, att)       
       repr' (Left g) = Sk g
       repr' (Right (x, att)) = Att att $ repr x 
       teqs' = Prelude.concatMap (\(e, EQ (lhs,rhs)) -> Prelude.map (\x -> EQ (nf'' this $ subst' lhs x, nf'' this $ subst' rhs x)) (Set.toList $ en e)) $ Set.toList $ obs_eqs sch
       teqs = Set.union (Set.fromList teqs') (Set.map (\(EQ (lhs,rhs)) -> EQ (nf'' this lhs, nf'' this rhs)) (Set.filter hasTypeType' $ eqs p))


subst' :: Term () ty sym en fk att Void Void -> GTerm en fk gen -> Term Void ty sym en fk att gen sk
subst' (Var ()) t = up t
subst' (Gen f) t = absurd f
subst' (Sk f) t = absurd f
subst' (Sym fs a) t = Sym fs (Prelude.map (\x -> subst' x t) a) 
subst' (Att f a) t = Att f $ subst' a t
subst' (Fk f a) t = Fk f $ subst' a t



hasTypeType :: Term Void ty sym en fk att gen sk -> Bool
hasTypeType (Var f) = absurd f
hasTypeType (Sym f as) = True
hasTypeType (Att f a) = True
hasTypeType (Sk f) = True
hasTypeType (Gen f) = False
hasTypeType (Fk f a) = False

hasTypeType' :: EQ Void ty sym en fk att gen sk -> Bool
hasTypeType' (EQ (lhs, rhs)) = hasTypeType lhs

       
fromListAccum :: (Ord v, Ord k) => [(k, v)] -> Map k (Set v)
fromListAccum [] = Map.empty
fromListAccum ((k,v):tl) = case Map.lookup k r of
   Just s -> Map.insert k (Set.insert v s) r 
   Nothing -> Map.insert k (Set.singleton v) r
  where r = fromListAccum tl

assembleSks :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Show en, Ord en) 
 => Collage var ty sym en fk att gen sk -> Map en (Set (GTerm en fk gen)) ->
 Map ty (Set (TTerm en fk att gen sk))
assembleSks col ens = unionWith Set.union sks $ fromListAccum gens
 where gens = Prelude.concatMap (\(en,set) -> Prelude.concatMap (\term -> Prelude.concatMap (\(att,ty) -> [(ty,(Right) (term,att))]) $ attsFrom col en) $ Set.toList $ set) $ Map.toList $ ens
       sks = Prelude.foldr (\(sk,t) m -> Map.insert t (Set.insert (Left sk) (lookup2 t m)) m) ret $ Map.toList $ csks col
       ret = Map.fromList $ Prelude.map (\x -> (x,Set.empty)) $ Set.toList $ ctys col


type GTerm en fk gen = Term Void Void Void en fk Void gen Void

type TTerm en fk att gen sk = Either sk (GTerm en fk gen, att)

fksFrom :: Eq en => Collage var ty sym en fk att gen sk -> en -> [fk]
fksFrom sch en = f $ Map.assocs $ cfks sch
  where f [] = []
        f ((fk,(en1,_)):l) = if en1 == en then fk : (f l) else f l


attsFrom :: Eq en => Collage var ty sym en fk att gen sk -> en -> [(att,ty)]
attsFrom sch en = f $ Map.assocs $ catts sch
  where f [] = []
        f ((fk,(en1,t)):l) = if en1 == en then (fk,t) : (f l) else f l


assembleGens :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en) 
 => Collage var ty sym en fk att gen sk -> [ GTerm en fk gen ] -> Map en (Set (GTerm en fk gen))
assembleGens col [] = Map.fromList $ Prelude.map (\x -> (x,Set.empty)) $ Set.toList $ cens col
assembleGens col (e:tl) = Map.insert t (Set.insert e s) m
 where m = assembleGens col tl
       t = typeOf col e
       s = case Map.lookup t m of
            Just s -> s
            Nothing -> undefined --impossible
       

--ex: x -> 
close :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en)
 => Collage var ty sym en fk att gen sk -> (EQ var ty sym en fk att gen sk -> Bool) -> [ (Term Void Void Void en fk Void gen Void) ]
close col dp = y (close1m dp col) $ Prelude.map Gen $ Map.keys $ cgens col
 where y f x = let z = f x in if x == z then x else y f z

close1m dp col = concatMap (close1 col dp)

dedup dp = nubBy (\x y -> dp (EQ (up x, up y)))

close1 :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en)
 => Collage var ty sym en fk att gen sk -> (EQ var ty sym en fk att gen sk -> Bool) -> Term Void Void Void en fk Void gen Void -> [ (Term Void Void Void en fk Void gen Void) ]
close1 col dp e = e : (dedup dp $ Prelude.map (\x -> Fk x e) l) 
 where t = typeOf col e
       l = fksFrom col t
      -- f [] = 

 
typeOf :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en)
  => Collage var ty sym en fk att gen sk -> Term Void Void Void en fk Void gen Void -> en
typeOf col e = case typeOf' col Map.empty (up e) of
  Left _ -> undefined
  Right x -> case x of
               Left _ -> undefined
               Right y -> y

up :: Term Void Void Void en fk Void gen Void -> Term var ty sym en fk att gen sk
up (Var f) = absurd f
up (Sym f x) = absurd f
up (Fk f a) = Fk f $ up a
up (Att f a) = absurd f
up (Gen f) = Gen f
up (Sk f) = absurd f



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


