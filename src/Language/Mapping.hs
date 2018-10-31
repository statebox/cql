{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Mapping where
import Prelude hiding (EQ)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Language.Term
import Language.Schema as Schema
import Data.Void
import Language.Common
import Data.Typeable
import qualified Data.Set as Set
import Data.Maybe


data Mapping var ty sym en fk att en' fk' att'
  = Mapping
  { src  :: Schema var ty sym en  fk  att
  , dst  :: Schema var ty sym en' fk' att'

  , ens  :: Map en  en'
  , fks  :: Map fk  (Term () Void Void en' fk' Void Void Void)
  , atts :: Map att (Term () ty   sym  en' fk' att' Void Void)
  }

getEns :: Mapping var ty sym en fk att en' fk' att' -> Map en  en'
getEns = ens

getFks :: Mapping var ty sym en fk att en' fk' att' -> Map fk  (Term () Void Void en' fk' Void Void Void)
getFks = fks

getAtts :: Mapping var ty sym en fk att en' fk' att' -> Map att (Term () ty   sym  en' fk' att' Void Void)
getAtts = atts

mapToMor
  :: ShowOrd9 var ty sym en fk att en' fk' att'
  => Mapping var ty sym en fk att en' fk' att'
  -> Morphism var ty sym en fk att Void Void en' fk' att' Void Void
mapToMor (Mapping src' dst' ens' fks' atts') = Morphism (schToCol src') (schToCol dst') ens' fks' atts' Map.empty Map.empty

data MappingEx :: * where
  MappingEx
    :: forall var ty sym en fk att en' fk' att' . (ShowOrdTypeable9 var ty sym en fk att en' fk' att')
    => Mapping var ty sym en fk att en' fk' att'
    -> MappingEx

deriving instance Show MappingEx


instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att')
  => Show (Mapping var ty sym en fk att en' fk' att') where
  show (Mapping _ _ ens' fks' atts') =
    "mapping {" ++ "\n" ++
    "entities" ++ "\n" ++
    "\t" ++ intercalate "\n\t" ens'' ++ "\n" ++
    "foreign_keys\n" ++
    "\t" ++ intercalate "\n\t" fks'' ++ "\n" ++
    "attributes\n" ++
    "\t" ++ intercalate "\n\t" atts'' ++ "\n" ++
    "}\n"
    where ens''  = (\(s,t) -> show s ++ " -> " ++ show t) <$> Map.toList ens'
          fks''  = (\(k,s) -> show k ++ " -> " ++ show s) <$> Map.toList fks'
          atts'' = (\(k,s) -> show k ++ " -> " ++ show s) <$> Map.toList atts'

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq en', Eq fk', Eq att')
  => Eq (Mapping var ty sym en fk att en' fk' att') where
  (Mapping s1' s2' ens' fks' atts') == (Mapping s1'' s2'' ens'' fks'' atts'')
    = (s1' == s1'') && (s2' == s2'') && (ens' == ens'') && (fks' == fks'') && (atts' == atts'')

typecheckMapping
  :: (ShowOrd2 var ty, ShowOrdTypeable7 sym en fk att en' fk' att')
  => Mapping var ty sym en fk att en' fk' att'
  -> Err ()
typecheckMapping m =  typeOfMor $ mapToMor m


validateMapping
  :: forall var ty sym en fk att en' fk' att' . (ShowOrd2 var ty, ShowOrdTypeable7 sym en fk att en' fk' att')
  => Mapping var ty sym en fk att en' fk' att'
  -> Err ()
validateMapping (m@(Mapping src' dst' ens' _ _)) = do _ <- mapM g (Set.toList $ path_eqs src')
                                                      _ <- mapM f (Set.toList $ obs_eqs src')
                                                      pure ()
 where f :: (en, EQ () ty sym en fk att Void Void) -> Err ()
       f (enx, EQ (l,r)) = let l' = trans (mapToMor m) l
                               r' = trans (mapToMor m) r :: Term () ty sym en' fk' att' Void Void
                               en'= fromJust $ Map.lookup enx ens'
                          in if eq dst' en' (EQ ( l',   r'))
                             then pure ()
                             else Left $ show l ++ " = " ++ show r ++ " translates to " ++ show l' ++ " = " ++ show r' ++ " which is not provable"
       g :: (en, EQ () Void Void en fk Void Void Void) -> Err ()
       g (enx, EQ (l,r)) = let l' = trans' (mapToMor m) l
                               r' = trans' (mapToMor m) r :: Term () Void Void en' fk' Void Void Void
                               en'= fromJust $ Map.lookup enx ens'
                          in if eq dst' en' (EQ (up13 l', up13 r'))
                             then pure ()
                             else Left $ show l ++ " = " ++ show r ++ " translates to " ++ show l' ++ " = " ++ show r' ++ " which is not provable"

trans' :: forall var var' ty sym en fk att gen sk en' fk' att' gen' sk' .
 (Ord gen, Ord sk, Ord fk, Eq var, Ord att, Ord var') =>
 Morphism var ty sym en fk att gen sk en' fk' att' gen' sk' ->
 Term var' Void Void en fk Void gen Void -> Term var' Void Void en' fk' Void gen' Void
trans' _ (Var x) = Var x
trans' mor (Fk f a) = let x = trans' mor a :: Term var' Void Void en' fk' Void gen' Void
                          y = fromJust $ Map.lookup f $ m_fks mor :: Term () Void Void en' fk' Void Void Void
                     in subst (up13 y) x
trans' _ (Sym _ _) = undefined
trans' _ (Att _ _) = undefined
trans' mor (Gen g) = up12 $ fromJust $ Map.lookup g (m_gens mor)
trans' _ (Sk _) = undefined


trans'' :: forall var var' ty sym en fk att gen en' fk' att' x .
 (Ord gen, Ord fk, Eq var, Ord att, Ord var') =>
 Morphism var ty sym en fk att Void Void en' fk' att' Void Void ->
 Term var' Void Void en fk Void (x,gen) Void -> Term var' Void Void en' fk' Void gen Void
trans'' _ (Var x) = Var x
trans'' mor (Fk f a) = let x = trans'' mor a :: Term var' Void Void en' fk' Void gen Void
                           y = fromJust $ Map.lookup f $ m_fks mor  :: Term () Void Void en' fk' Void Void Void
                     in subst (up13 y) x
trans'' _ (Sym _ _) = undefined
trans'' _ (Att _ _) = undefined
trans'' _ (Gen (_,g)) = Gen g
trans'' _ _ = undefined

data MappingExp where
  MappingVar     :: String -> MappingExp
  MappingId      :: SchemaExp -> MappingExp
  MappingRaw     :: MappingExpRaw' -> MappingExp
 deriving (Eq, Show)

getOptionsMapping :: MappingExp -> [(String, String)]
getOptionsMapping (MappingVar _) = []
getOptionsMapping (MappingId _) = []
getOptionsMapping (MappingRaw (MappingExpRaw' _ _ _ _ _ o _)) = o

instance Deps MappingExp where
 deps (MappingVar v) = [(v, MAPPING)]
 deps (MappingId s) = deps s
 deps (MappingRaw (MappingExpRaw' s t _ _ _ _ i)) = (deps s) ++ (deps t) ++ concatMap deps i

data MappingExpRaw' =
  MappingExpRaw'
  { mapraw_src     :: SchemaExp
  , mapraw_dst     :: SchemaExp
  , mapraw_ens     :: [(String, String)]
  , mapraw_fks     :: [(String, [String])]
  , mapraw_atts    :: [(String, (String, Maybe String, RawTerm)+[String])]
  , mapraw_options :: [(String, String)]
  , mapraw_imports :: [MappingExp]
} deriving (Eq, Show)

--todo: combine with schema
conv''
  :: forall ty ty2
   . (Typeable ty,Show ty, Typeable ty2, Show ty2)
  => [(String, String)]
  -> Err [(ty2, ty)]
conv'' [] = pure []
conv'' ((ty2,ty):tl) = case cast ty :: Maybe ty of
   Just ty' -> do x <- conv'' tl
                  case cast ty2 :: Maybe ty2 of
                    Just ty2' -> return $ (ty2', ty'):x
                    Nothing -> Left $ "Not in source schema/typeside: " ++ show ty2
   Nothing -> Left $ "Not in target schema/typeside: " ++ show ty

elem' :: (Typeable t, Typeable a, Eq a) => t -> [a] -> Bool
elem' x ys = maybe False (flip elem ys) (cast x)

member' :: (Typeable t, Typeable a, Eq a) => t -> Map a v -> Bool
member' k m = elem' k (Map.keys m)

mergeMaps :: Ord k => [Map k v] -> Map k v
mergeMaps [] = Map.empty
mergeMaps (x:y) = Map.union x $ mergeMaps y

evalMappingRaw'
  :: forall var ty sym en fk att en' fk' att' . (ShowOrd2 var ty, ShowOrdTypeable7 sym en fk att en' fk' att')
  => Schema var ty sym en fk att -> Schema var ty sym en' fk' att'
  -> MappingExpRaw'
  -> [Mapping var ty sym en fk att en' fk' att']
  -> Err (Mapping var ty sym en fk att en' fk' att')
evalMappingRaw' src' dst' (MappingExpRaw' _ _ ens0 fks0 atts0 _ _) is =
  do ens1 <- conv'' ens0
     ens2 <- toMapSafely ens1
     x <- k  fks0
     y <- f (q ens2) atts0
     return $ Mapping src' dst' (q ens2) (mergeMaps $ x:(map getFks is)) (mergeMaps $ y:(map getAtts is))
 where
  q ensX = Map.fromList $ (Map.toList ensX) ++ (concatMap (Map.toList . getEns) is)
  keys' = fst . unzip
  fks' = Map.toList $ Schema.fks dst'
  ens' = Set.toList $ Schema.ens dst'
  atts' = Map.toList $ Schema.atts dst'
  transE ens2 en = case (Map.lookup en ens2) of
                    Just x -> return x
                    Nothing -> Left $ "No entity mapping for " ++ (show en)

  f _ [] = pure $ Map.empty
  f x ((att, Right l):ts) = do
    att' <- note ("Not a src attribute " ++ att) (cast att)
    att2 <- note ("Not a dst attribute " ++ att) (cast $ head $ reverse l)
    t'x  <- h ens' $ tail $ reverse l
    let t'  = Att att2 $ up13 t'x
    rest <- f x ts
    pure $ Map.insert att' t' rest

  f x ((att, Left (v, t2, t)):ts) = do
    att' <- note ("Not an attribute " ++ att) (cast att)
    t'   <- return $ g v (keys' fks') (keys' atts') t
    rest <- f x ts
    let ret = pure $ Map.insert att' t' rest
        (s,_) = fromJust $ Map.lookup att' $ Schema.atts src'
    s' <- transE x s
    case t2 of
      Nothing -> ret
      Just t3 -> case cast t3 of
        Nothing -> Left $ "Not an entity: " ++ t3
        Just t4 -> if t4 == s'
                   then ret
                   else Left $ "Type mismatch: " ++ show s' ++ " and " ++ show t3
  --g' :: String ->[String]-> [String] -> RawTerm-> Term () Void Void en Fk Void  Void Void
  g' v _ _ (RawApp x []) | v == x = Var ()
  g' v fks'' atts'' (RawApp x (a:[])) | elem' x fks'' = Fk (fromJust $ cast x) $ g' v fks'' atts'' a
  g' _ _ _ _ = undefined
  g :: Typeable sym => String ->[fk']-> [att'] -> RawTerm -> Term () ty sym en' fk' att' Void Void
  g v _ _ (RawApp x []) | v == x = Var ()
  g v fks'' atts'' (RawApp x (a:[])) | elem' x fks'' = Fk (fromJust $ cast x) $ g' v fks'' atts'' a
  g v fks'' atts'' (RawApp x (a:[])) | elem' x atts'' = Att (fromJust $ cast x) $ g' v fks'' atts'' a
  g u fks'' atts'' (RawApp v l) = let l' = Prelude.map (g u fks'' atts'') l
                              in case cast v of
                                  Just x -> Sym x l'
                                  Nothing -> error "impossible until complex typesides"
  --h :: [en'] -> [String] -> Err (Term () Void Void en' fk' Void Void Void)
  h ens'' (s:ex) | elem' s ens'' = h ens'' ex
  h ens'' (s:ex) | elem' s (keys' fks') = do { h' <- h ens'' ex ; return $ Fk (fromJust $ cast s) h' }
               | otherwise = Left $ "Not a target fk: " ++ s
  h _ [] = return $ Var ()
 -- k :: [(String, [String])] -> Err (Map fk (Term () Void Void en' fk' Void Void Void))
  k  [] = pure $ Map.empty
  k  ((fk,p):eqs') = do
    p' <- h ens' $ reverse p
--    _ <- findEn ens' fks' p
    rest <- k  eqs'
    fk' <- note ("Not a src fk: " ++ fk) (cast fk)
    pure $ Map.insert fk' p' rest
  --findEn ens'' _ (s:_) | elem' s ens'' = return $ fromJust $ cast s
  --findEn _ fks'' (s:_) | elem' s (keys' $ fks'') = return $ fst $ fromJust $ Prelude.lookup (fromJust $ cast s) fks''
  --findEn ens'' fks'' (_:ex) | otherwise = findEn ens'' fks'' ex
  --findEn _ _ x = Left $ "Path cannot be typed: " ++ (show x)

evalMappingRaw
  :: (ShowOrdTypeable9 var ty sym en fk att en' fk' att')
  => Schema var ty sym en  fk  att
  -> Schema var ty sym en' fk' att'
  -> MappingExpRaw'
  -> [MappingEx]
  -> Err MappingEx
evalMappingRaw src' dst' t is =
 do (a :: [Mapping var ty sym en fk att en' fk' att']) <- g is
    r <- evalMappingRaw' src' dst' t a
    --l <- toOptions $ mapraw_options t
    pure $ MappingEx r
 where
   g :: forall var ty sym en fk att en' fk' att'. (Typeable var, Typeable ty, Typeable sym, Typeable en, Typeable fk, Typeable att, Typeable fk', Typeable en', Typeable att')
    => [MappingEx] -> Err [Mapping var ty sym en fk att en' fk' att']
   g [] = return []
   g ((MappingEx ts):r) = case cast ts of
                            Nothing -> Left "Bad import"
                            Just ts' -> do r'  <- g r
                                           return $ ts' : r'





