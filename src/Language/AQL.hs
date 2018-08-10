{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators #-}

module Language.AQL where

import Prelude hiding (EQ)
import Data.Set as Set
import Data.Map.Strict as Map
import Data.Void
import Data.List (intercalate)

-- kinds ---------------
data Kind = 
 --  CONSTRAINTS
   TYPESIDE
 | SCHEMA
 | INSTANCE
 | MAPPING
 | TRANSFORM
 | QUERY 
 -- | COMMAND 
 -- | GRAPH
 -- | COMMENT
 -- | SCHEMA_COLIMIT
 
-- operations defined across all AQL semantic objects of all kinds
class Semantics c t col where
  typeOf :: c -> t  
  validate :: c -> Maybe String 
  toCollage :: c -> col 
  kind :: Kind
  


   
type a + b = Either a b

-- Terms and theories --------------------------------------

data Term var ty sym en fk att gen sk
  = Var var
  | Sym sym  [Term var ty sym en fk att gen sk]
  | Fk  fk   (Term var ty sym en fk att gen sk)
  | Att att  (Term var ty sym en fk att gen sk)
  | Gen gen
  | Sk  sk

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) =>
  Show (Term var ty sym en fk att gen sk)
  where
    show x = case x of
     Var v      -> show v
     Gen g      -> show g
     Sk  s      -> show s
     Fk  fk  a  -> show a ++ "." ++ show fk
     Att att a  -> show a ++ "." ++ show att
     Sym sym az -> show sym ++ "(" ++ (intercalate "," . fmap show $ az) ++ ")"

deriving instance (Eq var, Eq sym, Eq fk, Eq att, Eq gen, Eq sk) => Eq (Term var ty sym en fk att gen sk)

deriving instance (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk) => Ord (Term var ty sym en fk att gen sk)

-- TODO wrap Map class to throw an error (or do something less ad hoc) if a key is ever put twice
type Ctx k v = Map k v

newtype EQ var ty sym en fk att gen sk
  = EQ ( Term var ty sym en fk att gen sk
       , Term var ty sym en fk att gen sk
       ) deriving Eq

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) => Show (EQ var ty sym en fk att gen sk) where
  show (EQ (lhs,rhs)) = show lhs ++ " = " ++ show rhs

data Collage var ty sym en fk att gen sk
  = Collage
  { eqs  :: EQ var ty sym en fk att gen sk
  , tys  :: Set ty
  , ens  :: Set en
  , fks  :: Map fk (en, en)
  , atts :: Map att (en, ty)
  , gens :: Map gen en
  , sks  :: Map sk ty
  } deriving (Eq, Show)

-- TODO
data Err1 t
  = CannotFindVar t
  | Undefined t

-- this is a non-Stringly typed version of typeOf
typeOf'
  :: (Ord var)
  => Collage var ty sym en fk att gen sk
  -> Ctx var (Either ty en)
  -> Term    var ty sym en fk att gen sk
  -> Either (Err1 (Term var ty sym en fk att gen sk)) (Either ty en)
typeOf' col ctx (Var varName) =
  note (CannotFindVar (Var varName)) (Map.lookup varName ctx)
  
-- Theorem proving ------------------------------------------------

data Prover = Free | Congruence | Orthogonal | KB

-- https://hackage.haskell.org/package/toysolver-0.0.4/src/src/Algorithm/CongruenceClosure.hs
-- http://hackage.haskell.org/package/twee
-- http://hackage.haskell.org/package/term-rewriting


--  Semantics -----------------------------------------------------------------

data Typeside var ty sym
  = Typeside
  { tys  :: Set ty
  , syms :: Map sym ([ty], ty)
  , eqs  :: Set (Ctx var ty, EQ var ty sym Void Void Void Void Void)
  , eq   :: Ctx var ty -> EQ var ty sym Void Void Void Void Void -> Bool

  {-- since we're in Haskell, a different DSL embedding strategy might be called for than the java version
  , hakell_tys   :: Map ty String
  , haskell_syms :: Map sym String
  --}
  }

instance (Eq var, Eq ty, Eq sym) => Eq (Typeside var ty sym) where
  (==) (Typeside tys  syms  eqs  eq)
       (Typeside tys' syms' eqs' eq')
    = (tys == tys') && (syms == syms') && (eqs == eqs')

instance (Show var, Show ty, Show sym) => Show (Typeside var ty sym) where
  show (Typeside tys syms eqs eq) =
    "tys = "    ++ show tys ++
    "\nsyms = " ++ show syms ++
    "\neqs = "  ++ show eqs

instance Semantics (Typeside var ty sym) () (Collage var ty sym Void Void Void Void Void) where
  typeOf = undefined -- todo
  validate = undefined 
  toCollage = undefined
  kind = TYPESIDE
  
--------------------------------------------------------------------------------

data Schema var ty sym en fk att
  = Schema
  { typeside :: Typeside var ty sym
  , ens      :: Set en
  , fks      :: Map fk (en, en)
  , atts     :: Map att (en, ty)
  , path_eqs :: Set (en, EQ () Void Void en fk Void Void Void)
  , obs_eqs  :: Set (en, EQ () ty   sym  en fk att  Void Void)
  , eq       :: en -> EQ () ty sym en fk att Void Void -> Bool
  }

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att)
  => Eq (Schema var ty sym en fk att) where
  (==) (Schema ts  ens  fks  atts  path_eqs  obs_eqs  eq)
       (Schema ts' ens' fks' atts' path_eqs' obs_eqs' eq')
    =  (ens == ens') && (fks == fks') && (atts == atts')
    && (path_eqs == path_eqs') && (obs_eqs == obs_eqs')
    && (ts == ts')

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att)
  => Show (Schema var ty sym en fk att) where
  show (Schema ts ens fks atts path_eqs obs_eqs eq) =
    "ens = " ++ (show ens) ++
    "\nfks = " ++ (show fks) ++ "\natts = " ++ (show atts) ++
    "\npath_eqs = " ++ (show path_eqs) ++ "\nobs_eqs = " ++ (show obs_eqs)

instance Semantics (Schema var ty sym en fk att) (Typeside var ty sym)  (Collage var ty sym en fk att Void Void) where
  typeOf = undefined -- todo
  validate = undefined 
  toCollage = undefined
  kind = SCHEMA

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
  show (Algebra _ ens fks atts nf repr nf' repr') =
    "ens = " ++ show ens ++
    "\nfks = " ++ show fks ++ "\natts = " ++ show atts

data Instance var ty sym en fk att gen sk x y
  = Instance
  { schema  :: Schema var ty sym en fk att
  , gens    :: Map gen en
  , sks     :: Map sk ty
  , eqs     :: Set (EQ Void ty sym en fk att gen sk)
  , eq      :: EQ var ty sym en fk att gen sk -> Bool

  , algebra :: Algebra var ty sym en fk att gen sk x y
  }

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y)
  => Show (Instance var ty sym en fk att gen sk x y) where
  show (Instance _ gens sks eqs eq _) =
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
    
instance Semantics (Instance var ty sym en fk att gen sk x y) (Schema var ty sym en fk att) (Collage var ty sym en fk att gen sk) where
  typeOf = undefined -- todo
  validate = undefined 
  toCollage = undefined
  kind = INSTANCE

-- adds one equation per fact in the algebra.
algebraToInstance
  :: Algebra var ty sym en fk att gen sk x y 
  -> Instance var ty sym en fk att gen sk x y  
algebraToInstance alg = undefined 

--------------------------------------------------------------------------------

data Mapping var ty sym en fk att en' fk' att'
  = Mapping
  { src  :: Schema var ty sym en  fk  att
  , dst  :: Schema var ty sym en' fk' att'

  , ens  :: Map en  en'
  , fks  :: Map fk  (Term () Void Void en' fk' Void Void Void)
  , atts :: Map att (Term () ty   sym  en' fk' att' Void Void)
  }

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att')
  => Show (Mapping var ty sym en fk att en' fk' att') where
  show (Mapping _ _ ens fks atts) =
    "ens = " ++ (show ens) ++
    "\nfks = " ++ (show fks) ++ "\natts = " ++ (show atts)

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq en', Eq fk', Eq att')
  => Eq (Mapping var ty sym en fk att en' fk' att') where
  (Mapping s1 s2 ens fks atts) == (Mapping s1' s2' ens' fks' atts')
    = (s1 == s1') && (s2 == s2') && (ens == ens') && (fks == fks') && (atts == atts')

validateMapping :: Mapping var ty sym en fk att en' fk' att' -> Maybe String
validateMapping = undefined

-- the type of the collage isn't quite right here
instance Semantics (Mapping var ty sym en fk att en' fk' att') (Schema var ty sym en fk att, Schema var ty sym en' fk' att') (Collage var ty sym (en+en') (fk+fk') (att+att') Void Void) where
  typeOf = undefined -- todo
  validate = undefined 
  toCollage = undefined
  kind = MAPPING

--------------------------------------------------------------------------------

data Query var ty sym en fk att en' fk' att'
  = Query
  { srcQ :: Schema var ty sym en fk att
  , dstQ :: Schema var ty sym en' fk' att'

  , ens  :: Map en' (Ctx var en, Set (EQ var ty sym en fk att Void Void))
  , fks  :: Map fk'  (Ctx var (Term var Void Void en fk Void Void Void))
  , atts :: Map att' (Term var ty   sym  en fk att  Void Void)
  }

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att')
  => Show (Query var ty sym en fk att en' fk' att') where
  show (Query _ _ ens fks atts) =
    "ens = " ++ show ens ++
    "\nfks = " ++ show fks ++ "\natts = " ++ show atts

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq en', Eq fk', Eq att')
  => Eq (Query var ty sym en fk att en' fk' att') where
  (==) (Query s1 s2 ens fks atts) (Query s1' s2' ens' fks' atts')
    = (s1 == s1') && (s2 == s2') && (ens == ens') && (fks == fks') && (atts == atts')
    
instance Semantics (Query var ty sym en fk att en' fk' att') (Schema var ty sym en fk att, Schema var ty sym en' fk' att') (Collage var ty sym (en+en') (fk+fk') (att+att') Void Void) where
  typeOf = undefined -- todo
  validate = undefined 
  toCollage = undefined
  kind = QUERY

--------------------------------------------------------------------------------

data Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  = Transform
  { srcT :: Instance var ty sym en fk att gen sk x y
  , dstT :: Instance var ty sym en fk att gen' sk' x' y'
  , gens :: Map gen (Term Void Void Void en fk Void gen' Void)
  , sks  :: Map sk  (Term var  ty   sym  en fk att  gen' sk')
  }

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Show gen', Show sk', Show x', Show y')
  => Show (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  show (Transform _ _ gens sks) =
    "gens = " ++ (show gens) ++
    "\nsks = " ++ (show sks)

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Eq x, Eq y, Eq gen', Eq sk', Eq x', Eq y')
  => Eq (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  (==) (Transform s1 s2 gens sks) (Transform s1' s2' gens' sks')
    = (s1 == s1') && (s2 == s2') && (gens == gens') && (sks == sks')

instance Semantics (Transform var ty sym en fk att gen sk x y gen' sk' x' y') (Instance var ty sym en fk att gen sk x y, Instance var ty sym en fk att gen' sk' x' y') (Collage var ty sym (en+en') (fk+fk') (att+att') (gen+gen') (sk+sk')) where
  typeOf = undefined -- todo
  validate = undefined 
  toCollage = undefined
  kind = TRANSFORM
  
-- Syntax ----------------------------------------------------------------------

-- todo: raw string based syntax with type inference, etc

-- todo: this recomputes the expressions associated with variables

class Syntax c t col where
  typeOf'' :: c -> t  
  validate' :: c -> Maybe String 
  eval :: c -> Program -> Env -> Either String col 
  kind' :: Kind
  deps :: c -> [(String,Kind)]
  
data Env = Env {
    typesides' :: forall var ty sym. Ctx String (Typeside var ty sym)
  , schemas' :: forall var ty sym en fk att. Ctx String (Schema var ty sym en fk att)
  , instances' :: forall var ty sym en fk att gen sk x y. Ctx String (Instance var ty sym en fk att gen sk x y)
  , mappings' :: forall var ty sym en fk att en' fk' att'. Ctx String (Mapping var ty sym en fk att en' fk' att')
  , queries' :: forall var ty sym en fk att en' fk' att'. Ctx String (Query var ty sym en fk att en' fk' att')
  , transforms' :: forall var ty sym en fk att gen sk x y gen' sk' x' y'. Ctx String (Transform var ty sym en fk att gen sk x y gen' sk' x' y')
}  

newEnv = Env m m m m m m
 where m = Map.empty

data Program = Program {
    order :: [(String,Kind)]
  , typesides :: forall var ty sym. Ctx String (TypesideExp var ty sym)
  , schemas :: forall var ty sym en fk att. Ctx String (SchemaExp var ty sym en fk att)
  , instances :: forall var ty sym en fk att gen sk x y. Ctx String (InstanceExp var ty sym en fk att gen sk x y)
  , mappings :: forall var ty sym en fk att en' fk' att'. Ctx String (MappingExp var ty sym en fk att en' fk' att')
  , queries :: forall var ty sym en fk att en' fk' att'. Ctx String (QueryExp var ty sym en fk att en' fk' att')
  , transforms :: forall var ty sym en fk att gen sk x y gen' sk' x' y'. Ctx String (TransformExp var ty sym en fk att gen sk x y gen' sk' x' y')
} 

--todo: help
lookupProg :: (Syntax c t col) => Program -> (String,Kind) -> Either String c
lookupProg p (v,k) = case k of
  TYPESIDE -> note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ typesides p
  SCHEMA -> note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ schemas p
  INSTANCE -> note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ instances p
  MAPPING -> note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ mappings p
  TRANSFORM -> note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ transforms p
  QUERY -> note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ queries p
  
newProg = Program [] m m m m m m
 where m = Map.empty

--todo: check acyclicit
runAqlProgram :: Program -> Either String Env
runAqlProgram p = case order p of 
                    [] -> pure newEnv
                    (v,k):l -> undefined

data TypesideExp :: * -> * -> * -> * where
  TypesideVar :: String -> TypesideExp var ty sym
  TypesideLiteral :: Typeside var ty sym -> TypesideExp var ty sym
  TypesideInitial :: TypesideExp Void Void Void
  

deriving instance (Eq var, Eq sym, Eq ty) => Eq (TypesideExp var ty sym)
deriving instance (Show var, Show sym, Show ty) => Show (TypesideExp var ty sym)

evalTypeside :: Program -> TypesideExp var ty sym -> Either String (Typeside var ty sym)
evalTypeside p (TypesideVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ typesides p 
                                    evalTypeside p n
evalTypeside p (TypesideLiteral typeside) = pure typeside
evalTypeside p  TypesideInitial           = pure $ Typeside Set.empty Map.empty Set.empty undefined -- todo: replace undefined with non effectful code

instance Syntax (TypesideExp var ty sym) () (Typeside var ty sym) where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = TYPESIDE
  deps = undefined
  
data SchemaExp :: * -> * -> * -> * -> * -> * -> * where
  SchemaVar :: String -> SchemaExp var ty sym en fk att
  SchemaLiteral :: Schema var ty sym en fk att -> SchemaExp var ty sym en fk att
  SchemaInitial :: Typeside var ty sym -> SchemaExp var ty sym en fk att
  SchemaCoProd  :: (SchemaExp var ty sym en                      fk              att)
                -> (SchemaExp var ty sym en'                        fk'              att')
                ->  SchemaExp var ty sym (Either en en') (Either fk fk') (Either att att')

evalSchema ctx (SchemaVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ schemas ctx 
                                  evalSchema ctx n
evalSchema ctx (SchemaLiteral schema)   = pure schema
evalSchema ctx (SchemaInitial typeside) = pure (Schema typeside Set.empty Map.empty Map.empty Set.empty Set.empty undefined)
evalSchema ctx (SchemaCoProd s1 s2) = Left "todo"
--todo: additional schema functions

instance Syntax (SchemaExp var ty sym en fk att) (TypesideExp var ty sym) (Schema var ty sym en fk att) where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = SCHEMA
  deps = undefined
  
data InstanceExp :: * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * where
  InstanceVar
    :: String
    -> InstanceExp var ty sym en fk att gen sk x y
  InstanceLiteral
    :: Instance var ty sym en fk att gen sk x y
    -> InstanceExp var ty sym en fk att gen sk x y
  InstanceInitial
    :: Schema var ty sym en fk att
    -> InstanceExp var ty sym en fk att Void Void Void Void

  InstanceDelta
    :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y, Eq en', Eq fk', Eq att')
    => MappingExp var ty sym en fk att en' fk' att'
    -> InstanceExp var ty sym en' fk' att' gen sk x y
    -> InstanceExp var ty sym en fk att (en',gen) sk (en',x) y

  InstanceSigma
    :: MappingExp  var ty sym en fk att en' fk' att'
    -> InstanceExp var ty sym en fk att gen sk x y
    -> InstanceExp var ty sym en fk att gen' sk' x' y'
  InstancePi
    :: MappingExp  var ty sym en fk att en' fk' att'
    -> InstanceExp var ty sym en fk att gen sk x y
    -> InstanceExp var ty sym en fk att gen' sk' x' y'
  InstanceEval
    :: QueryExp    var ty sym en fk att en' fk' att'
    -> InstanceExp var ty sym en fk att gen sk x y
    -> InstanceExp var ty sym en fk att gen' sk' x' y'
  InstanceCoEval
    :: MappingExp  var ty sym en fk att en' fk' att'
    -> InstanceExp var ty sym en fk att gen' sk' x' y'
    -> InstanceExp var ty sym en fk att gen sk x y


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

-- requires type signature for some reason
evalInstance :: Program -> InstanceExp var ty sym en fk att gen sk x y -> Either String (Instance var ty sym en fk att gen sk x y)
evalInstance ctx (InstanceVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ instances ctx 
                                      evalInstance ctx n
evalInstance ctx (InstanceDelta f' i') = do
  f <- evalMapping  ctx f'
  i <- evalInstance ctx i'
  if dst f == schema i
    then undefined --pure $ evalDeltaInst f i
    else Left $ "mapping has dst " -- todo ++ (show $ dst f) ++ " but insts schema is " ++ (show $ schema i)
evalInstance ctx (InstanceLiteral inst)   = pure inst
evalInstance ctx (InstanceInitial schema) = pure $
  Instance schema
           Map.empty Map.empty Set.empty undefined $ Algebra schema
           (Map.empty) undefined undefined
           undefined undefined undefined undefined
           --todo: undefineds can be replaced with actually non effectful code
evalInstance _ _ = Left ""

instance Syntax (InstanceExp var ty sym en fk att gen sk x y) (Schema var ty sym en fk att) (Instance var ty sym en fk att gen sk x y) where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = INSTANCE
  deps = undefined

data MappingExp  :: * -> * -> * -> * -> * -> * -> * -> * -> * -> * where
  MappingVar     :: String -> MappingExp var ty sym en fk att en' fk' att'
  MappingId      :: SchemaExp var ty sym en fk att              -> MappingExp var ty sym en fk att en  fk  att
  MappingLiteral :: Mapping   var ty sym en fk att en' fk' att' -> MappingExp var ty sym en fk att en' fk' att'

evalMapping ctx (MappingVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ mappings ctx 
                                    evalMapping ctx n
evalMapping ctx (MappingId schema) = Left "" --todo
evalMapping ctx (MappingLiteral l) = pure l

data QueryExp :: * -> * -> * -> * -> * -> * -> * -> * -> * -> * where
  QueryVar     :: String -> QueryExp var ty sym en fk att en' fk' att'
  QueryId      :: SchemaExp var ty sym en fk att              -> QueryExp var ty sym en fk att en  fk  att
  QueryLiteral :: Query     var ty sym en fk att en' fk' att' -> QueryExp var ty sym en fk att en' fk' att'

evalQuery
  :: Program -> QueryExp var ty sym en fk att en' fk' att'
  -> Either String (Query var ty sym en fk att en' fk' att')
evalQuery ctx (QueryVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ queries ctx 
                                evalQuery ctx n
evalQuery ctx (QueryId schema) = Left "" --todo
evalQuery ctx (QueryLiteral q) = pure q


instance Syntax (QueryExp var ty sym en fk att en' fk' att') (Schema var ty sym en fk att, Schema var ty sym en' fk' att') (Query var ty sym en fk att en' fk' att') where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = QUERY
  deps = undefined

data TransformExp :: * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * where
  TransformVar
    :: String -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y'
  TransformId
    :: InstanceExp  var ty sym en fk att gen sk x y
    -> TransformExp var ty sym en fk att gen sk x y gen sk x y
  TransformLiteral
    :: Transform    var ty sym en fk att gen sk x y gen' sk' x' y'
    -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y'

  --these types could be a little off
  TransformSigmaDeltaUnit
    :: MappingExp   var ty sym en fk att en' fk' att'
    -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y'
  TransformSigmaDeltaCoUnit
    :: MappingExp   var ty sym en fk att en' fk' att'
    -> TransformExp var ty sym en fk' att' gen' sk x y gen' sk' x' y'
  TransformDeltaPiUnit
    :: MappingExp   var ty sym en fk att en' fk' att'
    -> TransformExp var ty sym en fk' att' gen' sk x y gen' sk' x' y'
  TransformDeltaPiCoUnit
    :: MappingExp   var ty sym en fk att en' fk' att'
    -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y'
  TransformQueryUnit
    :: QueryExp     var ty sym en fk att en' fk' att'
    -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y'
  TransformQueryCoUnit
    :: MappingExp   var ty sym en fk  att  en' fk' att'
    -> TransformExp var ty sym en fk' att' gen' sk x y gen' sk' x' y'

  TransformDelta
    :: MappingExp   var ty sym en  fk  att  en' fk' att'
    -> TransformExp var ty sym en' fk' att' gen sk x y gen' sk' x' y'
    -> TransformExp var ty sym en  fk  att  gen sk x y gen' sk' x' y'
  TransformSigma
    :: MappingExp   var ty sym en  fk  att  en' fk' att'
    -> TransformExp var ty sym en  fk  att  gen sk x y gen' sk' x' y'
    -> TransformExp var ty sym en' fk' att' gen sk x y gen' sk' x' y'
  TransformPi
    :: MappingExp   var ty sym en  fk  att  en' fk' att'
    -> TransformExp var ty sym en  fk  att  gen sk x y gen' sk' x' y'
    -> TransformExp var ty sym en' fk' att' gen sk x y gen' sk' x' y'
  TransformCoEval
    :: QueryExp     var ty sym en  fk  att  en' fk' att'
    -> TransformExp var ty sym en' fk' att' gen sk x y gen' sk' x' y'
    -> TransformExp var ty sym en  fk  att  gen sk x y gen' sk' x' y'
  TransformEval
    :: QueryExp     var ty sym en  fk  att  en' fk' att'
    -> TransformExp var ty sym en  fk  att  gen sk x y gen' sk' x' y'
    -> TransformExp var ty sym en' fk' att' gen sk x y gen' sk' x' y'

evalTransform
  :: Program -> TransformExp             var ty sym en fk att gen sk x y gen' sk' x' y'
  -> Either String (Transform var ty sym en fk att gen sk x y gen' sk' x' y')
evalTransform ctx (TransformVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ transforms ctx 
                                        evalTransform ctx n
evalTransform ctx (TransformId inst  ) = Left "todo" --todo
evalTransform ctx (TransformLiteral h) = pure h

instance Syntax (TransformExp var ty sym en fk att gen sk x y gen' sk' x' y') (InstanceExp var ty sym en fk att gen sk x y, InstanceExp var ty sym en fk att gen' sk' x' y') (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = TRANSFORM
  deps = undefined

--------------------------------------------------------------------------------

-- generic helper inspired by https://pursuit.purescript.org/search?q=note
note :: b -> Maybe a -> Either b a
note n x = maybe (Left n) Right x
