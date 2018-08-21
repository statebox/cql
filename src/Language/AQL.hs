{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances #-}

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
  { ceqs  :: Set (EQ var ty sym en fk att gen sk)
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

data ProverName = Free | Congruence | Orthogonal | KB | Auto

data Prover var ty sym en fk att gen sk = Prover {
  collage :: Collage var ty sym en fk att gen sk
  , prove :: Ctx var (Either ty en) -> EQ var ty sym en fk att gen sk
   -> Bool
}

freeProver col = if (Set.size (ceqs col) == 0) 
                 then return $ Prover col p
                 else Left "Cannot use free prover when there are equations" 
 where p ctx (EQ (lhs, rhs)) = lhs == rhs

createProver ::  (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk) => ProverName -> Collage var ty sym en fk att gen sk 
  -> Either String (Prover var ty sym en fk att gen sk) 
createProver Free col = freeProver col
createProver _ _ = Left "Prover not available"
                           
--todo  

-- for ground theories: https://hackage.haskell.org/package/toysolver-0.0.4/src/src/Algorithm/CongruenceClosure.hs
-- for arbitrary theories: http://hackage.haskell.org/package/twee
-- for weakly orthogonal theories: http://hackage.haskell.org/package/term-rewriting


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

-- We should probably give serious thought to Idris, because Haskell's records and existentials
-- are broken, and AQL is innately dependently typed.  Anyway, the syntax types are highly parametric
-- to be helpful during manipulation, but they need to be 'sealed' at the top level in an AQL program,
-- so we have to build a wrapper like this bc of issues w impredicativity and RankN and whatnot. 
data TypesideEx :: * where  
 TypesideEx :: forall var ty sym. Typeside var ty sym -> TypesideEx
 
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


data SchemaEx :: * where
  SchemaEx :: forall var ty sym en fk att. Schema var ty sym en fk att -> SchemaEx

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

data InstanceEx :: * where
  InstanceEx :: forall var ty sym en fk att gen sk x y. Instance var ty sym en fk att gen sk x y -> InstanceEx


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
  
data MappingEx :: * where
  MappingEx :: forall var ty sym en fk att en' fk' att'. Mapping var ty sym en fk att en' fk' att' -> MappingEx

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


data QueryEx :: * where
  QueryEx :: forall var ty sym en fk att en' fk' att'. Query var ty sym en fk att en' fk' att' -> QueryEx

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

data TransformEx :: * where
  TransformEx :: forall var ty sym en fk att gen sk x y gen' sk' x' y' . 
    Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> TransformEx
  
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
    typesides' :: Ctx String (TypesideEx)
  , schemas' :: Ctx String (SchemaEx)
  , instances' :: Ctx String (InstanceEx)
  , mappings' :: Ctx String (MappingEx)
  , queries' :: Ctx String (QueryEx)
  , transforms' :: Ctx String (TransformEx)
}  

newEnv = Env m m m m m m
 where m = Map.empty

data Program = Program {
    typesides :: Ctx String (TypesideExp)
  , schemas ::  Ctx String (SchemaExp)
  , instances ::  Ctx String (InstanceExp)
  , mappings ::  Ctx String (MappingExp)
  , queries ::  Ctx String (QueryExp )
  , transforms ::  Ctx String (TransformExp )
} 

data Val :: * where
  Val :: (Semantics c t col) => c -> Val 
   
newProg = Program m m m m m m
 where m = Map.empty

--todo: check acyclic
evalAqlProgram :: [(String,Kind)] -> Program -> Env -> Either String Env
evalAqlProgram [] prog env = pure env
evalAqlProgram ((v,k):l) prog (env@(Env a b c d e f)) = 
 case k of 
  TYPESIDE -> do exp <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v (typesides prog)
                 ts <- evalTypeside prog env exp 
                 case ts of
                   TypesideEx ts2 -> let ts' = Map.insert v (TypesideEx ts2) $ typesides' env  in
                                      evalAqlProgram l prog $ env { typesides' = ts' }
  _ -> Left "Not implemented yet"

---------------------------------------------------------------------------------------- 

data TypesideExp where
  TypesideVar :: String -> TypesideExp
  TypesideInitial :: TypesideExp 
  
--typesideUnEx :: UNTYPABLE!
--typesideUnEx (TypesideExpEx x) = x --should be TypesideExpEx -> exists var ty sym. TypesideExp var ty sym
 
deriving instance (Eq var, Eq sym, Eq ty) => Eq (TypesideExp )
deriving instance (Show var, Show sym, Show ty) => Show (TypesideExp )

evalTypeside :: Program -> Env -> TypesideExp -> Either String (TypesideEx)
evalTypeside p env (TypesideVar v) = case Map.lookup v $ typesides' env of
  Nothing -> Left "todo"
  Just (TypesideEx e) -> Right $ TypesideEx e
evalTypeside p env TypesideInitial = pure $ TypesideEx $ Typeside Set.empty Map.empty Set.empty undefined -- todo: replace undefined with non effectful code

instance Syntax (TypesideExp) () (Typeside var ty sym) where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = TYPESIDE
  deps = undefined
  
------------------

data SchemaExp where
  SchemaVar :: String -> SchemaExp 
  SchemaLiteral :: Schema var ty sym en fk att -> SchemaExp
  SchemaInitial :: TypesideExp -> SchemaExp 
  SchemaCoProd  :: (SchemaExp )
                -> (SchemaExp )
                ->  SchemaExp 
                
  
evalSchema prog env (SchemaVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ schemas' env 
                                       pure n
evalSchema prog env (SchemaInitial ts) = do ts' <- evalTypeside prog env ts 
                                            case ts' of                                              
                                             TypesideEx ts'' -> 
                                               pure $ SchemaEx $ (Schema ts'' Set.empty Map.empty Map.empty Set.empty Set.empty undefined)
--evalSchema ctx (SchemaCoProd s1 s2) = Left "todo"
--todo: additional schema functions

instance Syntax (SchemaExp ) (TypesideExp ) (Schema var ty sym en fk att) where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = SCHEMA
  deps = undefined
  
data InstanceExp where
  InstanceVar
    :: String
    -> InstanceExp 
  InstanceLiteral
    :: Instance var ty sym en fk att gen sk x y
    -> InstanceExp 
  InstanceInitial
    :: SchemaExp 
    -> InstanceExp 

  InstanceDelta
    :: MappingExp 
    -> InstanceExp 
    -> InstanceExp 

  InstanceSigma
    :: MappingExp  
    -> InstanceExp 
    -> InstanceExp 
  InstancePi
    :: MappingExp  
    -> InstanceExp 
    -> InstanceExp 
  InstanceEval
    :: QueryExp    
    -> InstanceExp 
    -> InstanceExp 
  InstanceCoEval
    :: MappingExp  
    -> InstanceExp 
    -> InstanceExp 

--data InstanceExpEx :: * where 
 -- InstanceExpEx :: forall var ty sym en fk att gen sk x y. InstanceExp var ty sym en fk att gen sk x y -> InstanceExpEx 

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

evalInstance prog env (InstanceVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ instances' env 
                                           pure n
evalInstance prog env (InstanceInitial s) = do ts' <- evalSchema prog env s 
                                               case ts' of                                              
                                                 SchemaEx ts'' -> 
                                                  pure $ InstanceEx $ Instance ts''
                                                         Map.empty Map.empty Set.empty undefined $ Algebra ts''
                                                        (Map.empty) undefined undefined undefined undefined undefined undefined


instance Syntax (InstanceExp) (Schema var ty sym en fk att) (Instance var ty sym en fk att gen sk x y) where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = INSTANCE
  deps = undefined

data MappingExp   where
  MappingVar     :: String -> MappingExp 
  MappingId      :: SchemaExp         -> MappingExp

data QueryExp where
  QueryVar     :: String -> QueryExp 
  QueryId      :: SchemaExp              -> QueryExp 
  QueryLiteral :: Query     var ty sym en fk att en' fk' att' -> QueryExp 

evalMapping prog env (QueryVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ mappings' env 
                                       pure n




instance Syntax (QueryExp) (Schema var ty sym en fk att, Schema var ty sym en' fk' att') (Query var ty sym en fk att en' fk' att') where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = QUERY
  deps = undefined

data TransformExp  where
  TransformVar
    :: String -> TransformExp 
  TransformId
    :: InstanceExp  
    -> TransformExp 
  TransformLiteral
    :: Transform    var ty sym en fk att gen sk x y gen' sk' x' y'
    -> TransformExp 

  --these types could be a little off
  TransformSigmaDeltaUnit
    :: MappingExp   
    -> TransformExp 
  TransformSigmaDeltaCoUnit
    :: MappingExp   
    -> TransformExp 
  TransformDeltaPiUnit
    :: MappingExp   
    -> TransformExp 
  TransformDeltaPiCoUnit
    :: MappingExp   
    -> TransformExp 
  TransformQueryUnit
    :: QueryExp     
    -> TransformExp 
  TransformQueryCoUnit
    :: MappingExp   
    -> TransformExp

  TransformDelta
    :: MappingExp   
    -> TransformExp 
    -> TransformExp 
  TransformSigma
    :: MappingExp   
    -> TransformExp 
    -> TransformExp 
  TransformPi
    :: MappingExp   
    -> TransformExp 
    -> TransformExp 
  TransformCoEval
    :: QueryExp     
    -> TransformExp 
    -> TransformExp 
  TransformEval
    :: QueryExp     
    -> TransformExp 
    -> TransformExp 

instance Syntax (TransformExp) (InstanceExp , InstanceExp) (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = TRANSFORM
  deps = undefined
  

evalTransform prog env (TransformVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ transforms env 
                                             pure n



--------------------------------------------------------------------------------

-- generic helper inspired by https://pursuit.purescript.org/search?q=note
note :: b -> Maybe a -> Either b a
note n x = maybe (Left n) Right x
