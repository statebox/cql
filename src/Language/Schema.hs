{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitForAll        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImpredicativeTypes    #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.Schema where
import           Data.List         (nub)
import           Data.Map.Strict   as Map
import           Data.Maybe
import           Data.Set          as Set
import           Data.Typeable
import           Data.Void
import           Language.Common
import           Language.Options
import           Language.Prover
import           Language.Term
import           Language.Typeside
import           Prelude           hiding (EQ)
import           Control.DeepSeq


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

instance (NFData var, NFData ty, NFData sym, NFData en, NFData fk, NFData att) => NFData (Schema var ty sym en fk att) where
  rnf (Schema tys0 ens0 fks0 atts0 p0 o0 e0) = deepseq tys0 $ deepseq ens0 $ deepseq fks0 $ deepseq atts0 $ deepseq p0 $ deepseq o0 $ rnf e0

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att)
  => Eq (Schema var ty sym en fk att) where
  (==) (Schema ts'  ens'  fks'  atts'  path_eqs'  obs_eqs'  _)
       (Schema ts'' ens'' fks''  atts'' path_eqs'' obs_eqs'' _)
    =  (ens' == ens'') && (fks' == fks'') && (atts' == atts'')
    && (path_eqs' == path_eqs'') && (obs_eqs' == obs_eqs'')
    && (ts' == ts'')

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att)
  => Show (Schema var ty sym en fk att) where
  show (Schema _ ens' fks' atts' path_eqs' obs_eqs' _) = "schema {\n" ++
    "entities\n\t"  ++ intercalate "\n\t" (Prelude.map show $ Set.toList ens') ++
    "\nforeign_keys\n\t" ++ intercalate "\n\t" fks'' ++
    "\natts\n\t" ++ intercalate "\n\t" atts'' ++
    "\npath_equations\n\t" ++ intercalate "\n\t" (eqs'' path_eqs') ++
    "\nobservation_equations\n\t " ++ intercalate "\n\t" (eqs'' obs_eqs') ++ " }"
    where
      fks''   = Prelude.map (\(k,(s,t)) -> show k ++ " : " ++ show s ++ " -> " ++ show t) $ Map.toList fks'
      atts''  = Prelude.map (\(k,(s,t)) -> show k ++ " : " ++ show s ++ " -> " ++ show t) $ Map.toList atts'
      eqs'' x = Prelude.map (\(en,EQ (l,r)) -> "forall x : " ++ show en ++ " . " ++ show (mapVar "x" l) ++ " = " ++ show (mapVar "x" r)) $ Set.toList x

typecheckSchema
  :: (ShowOrdN '[var, ty, sym, en, fk, att])
  => Schema var ty sym en fk att
  -> Err ()
typecheckSchema t = typeOfCol $ schToCol  t

-- | Converts a schema to a collage.
schToCol
  :: (ShowOrdN '[var, ty, sym, en, fk, att])
  => Schema var ty sym en fk att
  -> Collage (() + var) ty sym en fk att Void Void
schToCol (Schema ts ens' fks' atts' path_eqs' obs_eqs' _) =
  Collage (Set.union e3 $ Set.union e1 e2) (ctys tscol)
    ens' (csyms tscol) fks' atts' Map.empty Map.empty
  where
    tscol = tsToCol ts
    e1 = Set.map (\(en, EQ (l,r))->(Map.fromList [(Left (),Right en)], EQ (upp l, upp r))) path_eqs'
    e2 = Set.map (\(en, EQ (l,r))->(Map.fromList [(Left (),Right en)], EQ (upp l, upp r))) obs_eqs'
    e3 = Set.map (\(g,EQ (l,r))->(up1Ctx g, EQ (upp l, upp r))) $ ceqs tscol

up1Ctx :: (Ord var) => Ctx var (ty+Void) -> Ctx (()+var) (ty+x)
up1Ctx g = Map.map (\x -> case x of
  Left ty -> Left ty
  Right v -> absurd v) $ Map.mapKeys Right g

typesideToSchema :: Typeside var ty sym -> Schema var ty sym Void Void Void
typesideToSchema ts'' = Schema ts'' Set.empty Map.empty Map.empty Set.empty Set.empty $ \x _ -> absurd x

fksFrom' :: (Show var, Eq en) => Schema var ty sym en fk att  -> en -> [(fk,en)]
fksFrom' sch en' = f $ Map.assocs $ fks sch
  where
    f []                 = []
    f ((fk, (en1, t)):l) = if en1 == en' then (fk,t) : (f l) else f l

attsFrom' :: Eq en => Schema var ty sym en fk att -> en -> [(att,ty)]
attsFrom' sch en' = f $ Map.assocs $ atts sch
  where
    f []                 = []
    f ((fk, (en1, t)):l) = if en1 == en' then (fk,t) : (f l) else f l

-- | Accessor due to namespace conflicts.
sch_fks :: Schema var ty sym en fk att -> Map fk (en, en)
sch_fks = fks

-- | Accessor due to namespace conflicts.
sch_atts :: Schema var ty sym en fk att -> Map att (en, ty)
sch_atts = atts

---------------------------------------------------------------------------------------------------
-- Expressions

data SchemaExp where
  SchemaVar     :: String                 -> SchemaExp
  SchemaInitial :: TypesideExp            -> SchemaExp
  SchemaCoProd  :: SchemaExp -> SchemaExp -> SchemaExp
  SchemaRaw     :: SchemaExpRaw'          -> SchemaExp
  deriving (Eq,Show)

getOptionsSchema :: SchemaExp -> [(String, String)]
getOptionsSchema x = case x of
  SchemaVar _                               -> []
  SchemaInitial  _                          -> []
  SchemaCoProd _ _                          -> []
  SchemaRaw (SchemaExpRaw' _ _ _ _ _ _ o _) -> o

instance Deps SchemaExp where
  deps x = case x of
    SchemaVar v                               -> [(v, SCHEMA)]
    SchemaInitial t                           -> deps t
    SchemaCoProd a b                          -> deps a ++ deps b
    SchemaRaw (SchemaExpRaw' t _ _ _ _ _ _ i) -> deps t ++ concatMap deps i

data SchemaEx :: * where
  SchemaEx
    :: forall var ty sym en fk att . (ShowOrdTypeableN '[var, ty, sym, en, fk, att])
    => Schema var ty sym en fk att
    -> SchemaEx

deriving instance Show (SchemaEx)

instance NFData SchemaEx where
  rnf (SchemaEx x) = rnf x

------------------------------------------------------------------------------------------------------
-- Literals

data SchemaExpRaw' = SchemaExpRaw'
  { schraw_ts      :: TypesideExp
  , schraw_ens     :: [String]
  , schraw_fks     :: [(String, (String, String))]
  , schraw_atts    :: [(String, (String, String))]
  , schraw_peqs    :: [([String], [String])]
  , schraw_oeqs    :: [(String, Maybe String, RawTerm, RawTerm)]
  , schraw_options :: [(String, String)]
  , schraw_imports :: [SchemaExp]
} deriving (Eq, Show)

-- | Type of entities for literal schemas.
type En = String

-- | Type of foreign keys for literal schemas.
type Fk = String

-- | Type of attributes for literal schemas.
type Att = String

evalSchemaRaw'
  :: (Show var, Ord var, ShowOrdTypeableN '[ty, sym])
  => Typeside var ty sym -> SchemaExpRaw'
  -> [Schema var ty sym En Fk Att]
  -> Err (Schema var ty sym En Fk Att)
evalSchemaRaw' x (SchemaExpRaw' _ ens'x fks'x atts'x peqs oeqs _ _) is = do
  ens''  <- return $ Set.fromList $ ie ++ ens'x
  fks''  <- toMapSafely $ fks'x  ++ (concatMap (Map.toList . fks) is)
  atts'2 <- convTys atts'x
  atts'' <- toMapSafely $ atts'2 ++ (concatMap (Map.toList . atts) is)
  peqs'  <- procPeqs (Set.toList ens'') (Map.toList fks'' ) peqs
  oeqs'  <- procOeqs (Map.toList fks'') (Map.toList atts'') oeqs
  return $ Schema x ens'' fks'' atts'' (Set.union ip peqs') (Set.union io oeqs') undefined --leave prover blank
  where
    ie = concatMap (Set.toList . ens) is
    ip = Set.fromList $ concatMap (Set.toList . path_eqs) is
    io = Set.fromList $ concatMap (Set.toList . obs_eqs ) is

    keys' = fst . unzip
    --f :: [(String, String, RawTerm, RawTerm)] -> Err (Set (En, EQ () ty   sym  en fk att  Void Void))
    procOeqs _ _ [] = pure $ Set.empty
    procOeqs fks' atts' ((v, en', lhs, rhs):eqs') = do
      en   <- infer v en' (Map.fromList fks') (Map.fromList atts') lhs rhs
      _    <- return $ Map.fromList [((),en)]
      lhs' <- return $ procTerm v (keys' fks') (keys' atts') lhs
      rhs' <- return $ procTerm v (keys' fks') (keys' atts') rhs
      rest <- procOeqs fks' atts' eqs'
      if not $ hasTypeType'' lhs'
        then Left $ "Bad obs equation: " ++ show lhs ++ " == " ++ show rhs
        else pure $ Set.insert (en, EQ (lhs', rhs')) rest

    infer _ (Just t) _    _     _   _   = return t
    infer v  _       fks' atts' lhs rhs = let
      t1s = nub $ typesOf v fks' atts' lhs
      t2s = nub $ typesOf v fks' atts' rhs
      in case (t1s, t2s) of
        (t1 : [], t2 : []) -> if t1 == t2 then return t1 else Left $ "Type mismatch on " ++ show v ++ " in " ++ show lhs ++ " = " ++ show rhs ++ ", types are " ++ show t1 ++ " and " ++ show t2
        (t1 : t2 : _, _) -> Left $ "Conflicting types for " ++ show v ++ " in " ++ show lhs ++ ": " ++ show t1 ++ " and " ++ show t2
        (_, t1 : t2 : _) -> Left $ "Conflicting types for " ++ show v ++ " in " ++ show rhs ++ ": " ++ show t1 ++ " and " ++ show t2
        ([], t : []) -> return t
        (t : [], []) -> return t
        ([], []) -> Left $ "Untypeable variable: " ++ show v

    typesOf _ _ _ (RawApp _ []) = []
    typesOf v fks' atts' (RawApp f' ((RawApp a []) : [])) | a == v = case Map.lookup f' fks' of
      Nothing      -> case Map.lookup f' atts' of
        Nothing    -> []
        Just (s,_) -> [s]
      Just (s,_)   -> [s]
    typesOf v fks' atts' (RawApp _ as) = concatMap (typesOf v fks' atts') as

    procTerm :: Typeable sym => String ->[String]-> [String] -> RawTerm-> Term () ty sym en Fk Att  Void Void
    procTerm v _ _ (RawApp x' []) | v == x' = Var ()
    procTerm v fks''' atts''' (RawApp x' (a:[])) | elem x' fks'''  = Fk  x' $ procTerm v fks''' atts''' a
    procTerm v fks''' atts''' (RawApp x' (a:[])) | elem x' atts''' = Att x' $ procTerm v fks''' atts''' a
    procTerm u fks''' atts''' (RawApp v l)                         = let l' = Prelude.map (procTerm u fks''' atts''') l
      in case cast v of
          Just x'' -> Sym x'' l'
          Nothing  -> error "impossible until complex typesides"

    procPath :: [String] -> [String] -> Term () Void Void En Fk Void Void Void
    procPath ens'' (s:ex) | elem s ens'' = procPath ens'' ex
    procPath ens'' (s:ex) | otherwise    = Fk s $ procPath ens'' ex
    procPath _ []                        = Var ()

    procPeqs _ _ [] = pure $ Set.empty
    procPeqs ens' fks' ((l,r):eqs') = do
      lhs' <- return $ procPath ens' $ reverse l
      rhs' <- return $ procPath ens' $ reverse r
      en   <- findEn ens' fks' l
      _    <- return $ Map.fromList [((),en)]
      rest <- procPeqs ens' fks' eqs'
      _    <- if hasTypeType'' lhs'
              then Left $ "Bad path equation: " ++ show lhs' ++ " = " ++ show rhs'
              else pure $ Set.insert (en, EQ (lhs', rhs')) rest
      pure $ Set.insert (en, EQ (lhs', rhs')) rest

    findEn ens'' _     (s:_ ) | elem s ens'' = return s
    findEn _     fks'' (s:_ ) | Map.member s (Map.fromList fks'') = return $ fst $ fromJust $ Prelude.lookup s fks''
    findEn ens'' fks'' (_:ex) | otherwise = findEn ens'' fks'' ex
    findEn _     _     []                 = Left "Path equation cannot be typed"

    convTys [] = return []
    convTys ((att, (en, ty)):tl) = case cast ty of
      Just ty' -> do
        xx <- convTys tl
        return $ (att, (en, ty')):xx
      Nothing -> Left $ "Not a type: " ++ show ty


evalSchemaRaw
  :: (ShowOrdTypeableN '[var, ty, sym])
  => Options
  -> Typeside var ty sym
  -> SchemaExpRaw'
  -> [SchemaEx]
  -> Err SchemaEx
evalSchemaRaw ops ty t a' = do
  (a :: [Schema var ty sym En Fk Att]) <- g a'
  r <- evalSchemaRaw' ty t a
  l <- toOptions ops $ schraw_options t
  p <- createProver (schToCol r) l
  pure $ SchemaEx $ Schema ty (ens r) (fks r) (atts r) (path_eqs r) (obs_eqs r) (f p)
  where
    f p en (EQ (l,r)) = prove p (Map.fromList [(Left (),Right en)]) (EQ (upp l, upp r))
    g [] = return []
    g ((SchemaEx ts):r) = case cast ts of
      Nothing -> Left $ "Bad import" ++ show ts
      Just ts' -> do { r'  <- g r ; return $ ts' : r' }
