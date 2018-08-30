{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.AQL where

import Prelude hiding (EQ)
import Data.Set as Set
import Data.Map.Strict as Map
import Data.Void
import Data.List (intercalate)

-- main = undefined

-- helpers

type a + b = Either a b

fromList' :: (Show k, Ord k) => [(k,v)] -> Err (Map k v) 
fromList' ((k,v):l) = do l' <- fromList' l 
                         if Map.member k l' 
                         then Left $ "Duplicate binding: " ++ (show k)
                         else pure $ Map.insert k v l'

fromList'' :: (Show k, Ord k) => [k] -> Err (Set k) 
fromList'' (k:l) = do l' <- fromList'' l 
                      if Set.member k l' 
                      then Left $ "Duplicate binding: " ++ (show k)
                      else pure $ Set.insert k l' 


-- top level stuff

-- simple three phase evaluation and reporting
runProg :: String -> Err (Prog, Types, Env)
runProg p = do p1 <- parseAqlProgram p
               o  <- findOrder p1
               p2 <- typecheckAqlProgram o p1
               p3 <- evalAqlProgram o p1 newEnv 
               return (p1, p2, p3)
             
parseAqlProgram :: String -> Err Prog
parseAqlProgram = undefined -- can be filled in now


-- kinds ---------------
data Kind = CONSTRAINTS | TYPESIDE | SCHEMA | INSTANCE | MAPPING | TRANSFORM | QUERY | COMMAND | GRAPH | COMMENT | SCHEMA_COLIMIT
 
-- operations defined across all AQL semantic objects of all kinds
class Semantics c  where
 -- typeOf :: c -> t  
 -- validate :: c -> Err () 
 -- toCollage :: c -> col 
 -- kind :: Kind for now these aren't coming up
     

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

-- Our own pair type for pretty printing purposes
newtype EQ var ty sym en fk att gen sk
  = EQ (Term var ty sym en fk att gen sk, Term var ty sym en fk att gen sk) deriving (Ord,Eq)

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) => Show (EQ var ty sym en fk att gen sk) where
  show (EQ (lhs,rhs)) = show lhs ++ " = " ++ show rhs

data Collage var ty sym en fk att gen sk
  = Collage
  { ceqs  :: Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk)
  , ctys  :: Set ty
  , cens  :: Set en
  , csyms :: Map sym ([ty],ty)
  , cfks  :: Map fk (en, en)
  , catts :: Map att (en, ty)
  , cgens :: Map gen en
  , csks  :: Map sk ty
  } deriving (Eq, Show)

-- TODO
--data Err1 t
--  = CannotFindVar t
--  | Undefined t

-- I've given up on non string based error handling for now
typeOf'
  :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> Ctx var (ty + en)
  -> Term    var ty sym en fk att gen sk
  -> Err (ty + en)
typeOf' col ctx (Var v) = note ("Unbound variable: " ++ show v) $ Map.lookup v ctx
typeOf' col ctx (Gen g) = case Map.lookup g $ cgens col of
  Nothing -> Left $ "Unknown generator: " ++ show g
  Just t -> pure $ Right t
typeOf' col ctx (Sk s) = case Map.lookup s $ csks col of
  Nothing -> Left $ "Unknown labelled null: " ++ show s
  Just t -> pure $ Left t
typeOf' col ctx (Fk f a) = case Map.lookup f $ cfks col of
  Nothing -> Left $ "Unknown foreign key: " ++ show f
  Just (s, t) -> do s' <- typeOf' col ctx a 
                    if (Right s) == s' then pure $ Right t else Left $ "Expected argument to have entity " ++
                     show s ++ " but given " ++ show s' 
typeOf' col ctx (Att f a) = case Map.lookup f $ catts col of
  Nothing -> Left $ "Unknown attribute: " ++ show f
  Just (s, t) -> do s' <- typeOf' col ctx a 
                    if (Right s) == s' then pure $ Left t else Left $ "Expected argument to have entity " ++
                     show s ++ " but given " ++ show s' 
typeOf' col ctx (Sym f a) = case Map.lookup f $ csyms col of
  Nothing -> Left $ "Unknown function symbol: " ++ show f
  Just (s, t) -> do s' <- mapM (typeOf' col ctx) a 
                    if length s' == length s
                    then if (fmap Left s) == s' 
                         then pure $ Left t
                         else Left $ "Expected arguments to have types " ++
                     show s ++ " but given " ++ show s' 
                    else Left $ "Expected argument to have arity " ++
                     show (length s) ++ " but given " ++ show (length s') 
                     
typeOfEq'
  :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> (Ctx var (ty + en), EQ var ty sym en fk att gen sk)
  -> Err (ty + en)
typeOfEq' col (ctx, EQ (lhs, rhs)) = do lhs' <- typeOf' col ctx lhs
                                        rhs' <- typeOf' col ctx rhs
                                        if lhs' == rhs'
                                        then pure lhs'
                                        else Left $ "Equation lhs has type " ++ show lhs' ++ " but rhs has type " ++ show rhs' 

checkDoms :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> Err ()
checkDoms col = do mapM f $ Map.elems $ csyms col
                   mapM g $ Map.elems $ cfks  col
                   mapM h $ Map.elems $ catts col 
                   mapM isEn $ Map.elems $ cgens col
                   mapM isTy $ Map.elems $ csks  col
                   pure ()
 where f (t1,t2) = do mapM isTy t1
                      isTy t2
       g (e1,e2) = do isEn e1 
                      isEn e2                     
       h (e,t) = do isEn e
                    isTy t
       isEn x = if Set.member x $ cens col
                then pure () 
                else Left $ "Not an entity: " ++ show x 
       isTy x = if Set.member x $ ctys col 
                then pure () 
                else Left $ "Not a type: " ++ show x 


typeOfCol
  :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> Err ()
typeOfCol col = do checkDoms col 
                   x <- mapM (typeOfEq' col) $ Set.toList $ ceqs col 
                   pure () 

--Set is not Traversable! Lame                 

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

createProver ::  (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk) 
 => ProverName -> Collage var ty sym en fk att gen sk 
  -> Err (Prover var ty sym en fk att gen sk) 
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

--instance Semantics (Typeside var ty sym) where
validateTypeside = typeOfCol . tsToCol
 
data RawTerm = RawApp String [RawTerm]
 deriving Eq
 
instance Show RawTerm where
 show (RawApp sym az) = show sym ++ "(" ++ (intercalate "," . fmap show $ az) ++ ")"
  
--todo: make validating Typeside function

--todo: parser should target these
data TypesideRaw' = TypesideRaw' {
--  tsraw_imports :: [TypesideExp -> Either String TypesideEx]  these are going to be nasty bc of the type system
   tsraw_tys  :: [String]
  , tsraw_syms :: [(String, ([String], String))]
  , tsraw_eqs  :: [([(String, String)], RawTerm, RawTerm)] 
  , tsraw_options :: [(String, String)]
} deriving (Eq, Show)

tsToCol :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym) => Typeside var ty sym -> Collage var ty sym Void Void Void Void Void
tsToCol (Typeside t s e _) = Collage e' t Set.empty s Map.empty Map.empty Map.empty Map.empty
 where e' = Set.map (\(g,x)->(Map.map Left g, x)) e

proverStringToName :: Map String String -> Err ProverName
proverStringToName m = case Map.lookup "prover" m of
 (Just "auto") -> pure Auto
 (Just "kb") -> pure KB
 (Just "program") -> pure Orthogonal
 (Just "congruence") -> pure Congruence
 (Just x) -> Left $ "Not a prover: " ++ x
 Nothing -> pure Auto

evalTypesideRaw :: TypesideRaw' -> Err TypesideEx
evalTypesideRaw t = 
 do r <- evalTypesideRaw' t
    o <- fromList' $ tsraw_options t
    n <- proverStringToName o
    p <- createProver n (tsToCol r)   
    pure $ TypesideEx $ Typeside (tys r) (syms r) (eqs r) (f p)
 where 
  f p ctx eq = prove p (Map.map Left ctx) eq    

evalTypesideRaw' :: TypesideRaw' -> Err (Typeside String String String)
evalTypesideRaw' (TypesideRaw' tys syms eqs ops) = 
  do tys' <- fromList'' tys
     syms' <- fromList' syms 
     eqs' <- f syms' eqs
     pure $ Typeside tys' syms' eqs' undefined -- leave prover blank
 where f syms' [] = pure $ Set.empty
       f syms' ((ctx, lhs, rhs):eqs') = do ctx' <- check ctx
                                           lhs' <- g syms' ctx' lhs  
                                           rhs' <- g syms' ctx' rhs
                                           rest <- f syms' eqs'
                                           pure $ Set.insert (ctx', EQ (lhs', rhs')) rest
       g syms' ctx (RawApp v []) | Map.member v ctx = pure $ Var v 
       g syms' ctx (RawApp v l) = do l' <- mapM (g syms' ctx) l
                                     pure $ Sym v l'        
       check [] = pure Map.empty
       check ((v,t):l) = if elem v tys then do {x <- check l; pure $ Map.insert v t x} else Left $ "Not a type: " ++ (show t)                                  


-- there are practical haskell type system related reasons to not want this to be a gadt 
data TypesideExp where
  TypesideVar :: String -> TypesideExp
  TypesideInitial :: TypesideExp 
  TypesideRaw :: TypesideRaw' -> TypesideExp
  
 
deriving instance (Eq var, Eq sym, Eq ty) => Eq TypesideExp
deriving instance (Show var, Show sym, Show ty) => Show TypesideExp

evalTypeside :: Prog -> Env -> TypesideExp -> Err TypesideEx
evalTypeside p env (TypesideRaw r) = evalTypesideRaw r
evalTypeside p env (TypesideVar v) = case Map.lookup v $ typesides env of
  Nothing -> Left $ "Undefined typeside: " ++ show v
  Just (TypesideEx e) -> Right $ TypesideEx e
evalTypeside p env TypesideInitial = pure $ TypesideEx $ Typeside Set.empty Map.empty Set.empty undefined -- todo: replace undefined with non effectful code


class Syntax c t col | c -> t, c -> col where
  typeOf'' :: c -> t  
  validate' :: c -> Err () 
  eval :: Prog -> Env -> c -> Err col 
  kind' :: Kind
  deps :: c -> [(String,Kind)]

instance Syntax TypesideExp () TypesideEx where
  typeOf'' = undefined
  validate' = undefined
  eval = evalTypeside 
  
  kind' = TYPESIDE
  
  deps (TypesideVar v) = [(v, TYPESIDE)]
  deps TypesideInitial = []
  deps (TypesideRaw r) = []

  
--------------------------------------------------------------------------------


data SchemaExp where
  SchemaVar :: String -> SchemaExp 
  SchemaInitial :: TypesideExp -> SchemaExp 
  SchemaCoProd  :: SchemaExp -> SchemaExp -> SchemaExp 
  SchemaRaw :: SchemaExpRaw' -> SchemaExp
                
  
evalSchema prog env (SchemaVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ schemas env 
                                       pure n
evalSchema prog env (SchemaInitial ts) = do ts' <- evalTypeside prog env ts 
                                            case ts' of                                              
                                             TypesideEx ts'' -> 
                                               pure $ SchemaEx $ (Schema ts'' Set.empty Map.empty Map.empty Set.empty Set.empty undefined)
--evalSchema ctx (SchemaCoProd s1 s2) = Left "todo"
--todo: additional schema functions

instance Syntax (SchemaExp ) (TypesideEx ) (SchemaEx) where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = SCHEMA
  deps = undefined

validateSchema = typeOfCol . schToCol
{--
data Collage var ty sym en fk att gen sk
  = Collage
  { ceqs  :: Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk)
  , ctys  :: Set ty
  , cens  :: Set en
  , csyms :: Map sym ([ty],ty)
  , cfks  :: Map fk (en, en)
  , catts :: Map att (en, ty)
  , cgens :: Map gen en
  , csks  :: Map sk ty
  } deriving (Eq, Show)
  --}
  
schToCol :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en, Show en, Ord fk, Show fk, Ord att, Show att) => Schema var ty sym en fk att -> Collage (()+var) ty sym en fk att Void Void
schToCol (Schema ts ens fks atts path_eqs obs_eqs _) = 
 Collage (Set.union e3 $ Set.union e1 e2) (ctys tscol) 
  ens (csyms tscol) fks atts Map.empty Map.empty
   where tscol = tsToCol ts
         e1 = Set.map (\(en, EQ (l,r))->(Map.fromList [(Left (),Right en)], EQ (up3 l, up3 r))) path_eqs
         e2 = Set.map (\(en, EQ (l,r))->(Map.fromList [(Left (),Right en)], EQ (up2 l, up2 r))) obs_eqs
         e3 = Set.map (\(g,EQ (l,r))->(up1Ctx g, EQ (up1 l, up1 r))) $ ceqs tscol
         
   
up2 :: Term () ty sym en fk att Void Void -> Term (()+var) ty sym en fk att x y
up2 (Var v) = Var $ Left () 
up2 (Sym f x) = Sym f $ Prelude.map up2 x
up2 (Fk f a) = Fk f $ up2 a   
up2 (Att f a) = Att f $ up2 a 
up2 (Gen f) = absurd f   
up2 (Sk f) = absurd f    
     
         
up3 :: Term () Void Void en fk Void Void Void -> Term (()+var) ty sym en fk att x y
up3 (Var v) = Var $ Left () 
up3 (Sym f x) = absurd f
up3 (Fk f a) = Fk f $ up3 a   
up3 (Att f a) = absurd f 
up3 (Gen f) = absurd f   
up3 (Sk f) = absurd f      
     
up1 :: Term var ty sym Void Void Void Void Void -> Term (()+var) ty sym en fk att x y
up1 (Var v) = Var $ Right v 
up1 (Sym f x) = Sym f $ Prelude.map up1 x
up1 (Fk f a) = absurd f   
up1 (Att f a) = absurd f 
up1 (Gen f) = absurd f   
up1 (Sk f) = absurd f   

up1Ctx :: (Ord var) => Ctx var (ty+Void) -> Ctx (()+var) (ty+x)
up1Ctx g = Map.map (\x -> case x of 
  Left ty -> Left ty 
  Right v -> absurd v) $ Map.mapKeys Right g

  

data SchemaExpRaw' = SchemaExpRaw' {
    schraw_ens  :: [String]
  , schraw_fks :: [(String, (String, String))]
  , schraw_atts:: [(String, (String, String))]
  , schraw_peqs  :: [(String, [String])] 
  , schraw_oeqs  :: [(String, (String, String, RawTerm))] 
  , schraw_options :: [(String, String)]
} deriving (Eq, Show)

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

--instance Semantics (Schema var ty sym en fk att)  where
 --validate = undefined 
 
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
    
--instance Semantics (Instance var ty sym en fk att gen sk x y)  where
 -- validate = undefined 
 
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
--instance Semantics (Mapping var ty sym en fk att en' fk' att')  where
--  validate = undefined 
 
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
    
--instance Semantics (Query var ty sym en fk att en' fk' att')  where
--  validate = undefined 
 
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
  
instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, 
          Show x, Show y, Show gen', Show sk', Show x', Show y')
  => Show (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  show (Transform _ _ gens sks) =
    "gens = " ++ (show gens) ++
    "\nsks = " ++ (show sks)

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Eq x, Eq y, Eq gen', Eq sk', Eq x', Eq y')
  => Eq (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  (==) (Transform s1 s2 gens sks) (Transform s1' s2' gens' sks')
    = (s1 == s1') && (s2 == s2') && (gens == gens') && (sks == sks')

--instance Semantics (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
--  validate = undefined 
  
-- Syntax ----------------------------------------------------------------------

-- todo: raw string based syntax with type inference, etc
  
data KindCtx ts s i m q t o = KindCtx {
    typesides :: Ctx String ts
  , schemas ::  Ctx String s
  , instances ::  Ctx String i
  , mappings ::  Ctx String m
  , queries ::  Ctx String q
  , transforms ::  Ctx String t
  , other :: o
}

--todo: store exception info in other field
type Env = KindCtx TypesideEx SchemaEx InstanceEx MappingEx QueryEx TransformEx ()

--todo: store line numbers in other field
type Prog = KindCtx TypesideExp SchemaExp InstanceExp MappingExp QueryExp TransformExp [(String,Kind)]

type Types = KindCtx () TypesideExp SchemaExp (SchemaExp,SchemaExp) (SchemaExp,SchemaExp) (InstanceExp,InstanceExp) ()

newEnv = KindCtx m m m m m m ()
 where m = Map.empty
   
newProg = KindCtx m m m m m m []
 where m = Map.empty
 
newTypes = KindCtx m m m m m m ()
 where m = Map.empty

type Err = Either String

lookup' m v = f $ Map.lookup m v
 where f (Just x) = x

--todo: might look nicer in state monad

-- some ordering - could be program order, but not necessarily
typecheckAqlProgram :: [(String,Kind)] -> Prog -> Err Types
typecheckAqlProgram [] prog = pure newTypes 
typecheckAqlProgram ((v,TYPESIDE):l) prog = do ts <- note ("Undefined AQL typeside: " ++ show v) $ Map.lookup v $ typesides prog
                                               typecheckAqlProgram l prog

validateAqlProgram :: [(String,Kind)] -> Prog -> Err ()
validateAqlProgram [] prog = pure ()
validateAqlProgram ((v,TYPESIDE):l) prog =  do x <- validate' $ lookup' v $ typesides prog
                                               validateAqlProgram l prog
                                                                                            

--todo: check acyclic with Data.Graph.DAG
evalAqlProgram :: [(String,Kind)] -> Prog -> Env -> Err Env
evalAqlProgram [] prog env = pure env
evalAqlProgram ((v,TYPESIDE):l) prog env = case lookup' v $ typesides env of
                                               TypesideEx ts2 -> let ts' = Map.insert v (TypesideEx ts2) $ typesides env  in
                                                                     evalAqlProgram l prog $ env { typesides = ts' }
 


findOrder :: Prog -> Err [(String, Kind)]
findOrder p = pure $ other p --todo: for now

-----------  
----------------------------------------------------------------------------------------------------------------------

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

evalInstance prog env (InstanceVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ instances env 
                                           pure n
evalInstance prog env (InstanceInitial s) = do ts' <- evalSchema prog env s 
                                               case ts' of                                              
                                                 SchemaEx ts'' -> 
                                                  pure $ InstanceEx $ Instance ts''
                                                         Map.empty Map.empty Set.empty undefined $ Algebra ts''
                                                        (Map.empty) undefined undefined undefined undefined undefined undefined


instance Syntax (InstanceExp) (SchemaEx) (InstanceEx) where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = INSTANCE
  deps = undefined

data MappingExp   where
  MappingVar     :: String -> MappingExp 
  MappingId      :: SchemaExp -> MappingExp
  MappingRaw     :: MapExpRaw' -> MappingExp

data MapExpRaw' = MapExpRaw' {
    mapraw_ens  :: [(String, String)]
  , mapraw_fks :: [(String, [String])]
  , mapraw_atts  :: [(String, (String, String, RawTerm))] 
  , mapraw_options :: [(String, String)]
} deriving (Eq, Show)


data QueryExp where
  QueryVar     :: String -> QueryExp 
  QueryId      :: SchemaExp -> QueryExp 
  QueryRaw     :: QueryExpRaw' -> QueryExp 


--old school queries without overlapping names across entities
data QueryExpRaw' = QueryExpRaw' {
    qraw_ens  :: [(String, ([(String,String)],[(RawTerm,RawTerm)]))]
  , qraw_fks :: [(String, [(String,RawTerm)])] 
  , qraw_atts  :: [(String, RawTerm)] 
  , qraw_options :: [(String, String)]
} deriving (Eq, Show)


evalMapping prog env (QueryVar v) = do n <- note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ mappings env 
                                       pure n




instance Syntax (QueryExp) (SchemaEx, SchemaEx) (QueryEx) where
  typeOf'' = undefined
  validate' = undefined
  eval = undefined 
  kind' = QUERY
  deps = undefined

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


instance Syntax (TransformExp) (InstanceExp , InstanceExp) (TransformEx) where
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
