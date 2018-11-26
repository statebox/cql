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
--{-# LANGUAGE DisambiguateRecordFields #-}

module Language.Mapping where
import           Control.DeepSeq
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import qualified Data.Set        as Set
import           Data.Typeable
import           Data.Void
import           Language.Common
import           Language.Schema as Schema
import           Language.Term
import           Prelude         hiding (EQ)

-- | Morphism of schemas.
data Mapping var ty sym en fk att en' fk' att'
  = Mapping
  { src  :: Schema var ty sym en  fk  att
  , dst  :: Schema var ty sym en' fk' att'

  , ens  :: Map en  en'
  , fks  :: Map fk  (Term () Void Void en' fk' Void Void Void)
  , atts :: Map att (Term () ty   sym  en' fk' att' Void Void)
  }

instance (NFData var, NFData ty, NFData sym, NFData en, NFData fk, NFData att, NFData en', NFData fk', NFData att')
  => NFData (Mapping var ty sym en fk att en' fk' att') where
  rnf (Mapping s t e f a) = deepseq s $ deepseq t $ deepseq e $ deepseq f $ rnf a

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att')
  => Show (Mapping var ty sym en fk att en' fk' att') where
  show (Mapping _ _ ens' fks' atts') =
    "mapping {" ++ "\n" ++
    "entities " ++ "\n" ++
    "\t" ++ intercalate "\n\t" ens''  ++ "\n" ++
    "foreign_keys\n" ++
    "\t" ++ intercalate "\n\t" fks''  ++ "\n" ++
    "attributes  \n" ++
    "\t" ++ intercalate "\n\t" atts'' ++ "\n" ++
    "}\n"
    where
      ens''  = (\(s,t) -> show s ++ " -> " ++ show t) <$> Map.toList ens'
      fks''  = (\(k,s) -> show k ++ " -> " ++ show s) <$> Map.toList fks'
      atts'' = (\(k,s) -> show k ++ " -> " ++ show s) <$> Map.toList atts'

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq en', Eq fk', Eq att')
  => Eq (Mapping var ty sym en fk att en' fk' att') where
  (Mapping s1' s2' ens' fks' atts') == (Mapping s1'' s2'' ens'' fks'' atts'')
    = (s1' == s1'') && (s2' == s2'') && (ens' == ens'') && (fks' == fks'') && (atts' == atts'')

-- | Accessor due to name conflict
getEns :: Mapping var ty sym en fk att en' fk' att' -> Map en  en'
getEns = ens

-- | Accessor due to name conflict
getFks :: Mapping var ty sym en fk att en' fk' att' -> Map fk  (Term () Void Void en' fk' Void Void Void)
getFks = fks

-- | Accessor due to name conflict
getAtts :: Mapping var ty sym en fk att en' fk' att' -> Map att (Term () ty   sym  en' fk' att' Void Void)
getAtts = atts

mapToMor
  :: ShowOrdN '[var, ty, sym, en, fk, att, en', fk', att']
  => Mapping var ty sym en fk att en' fk' att'
  -> Morphism var ty sym en fk att Void Void en' fk' att' Void Void
mapToMor (Mapping src' dst' ens' fks' atts') = Morphism (schToCol src') (schToCol dst') ens' fks' atts' Map.empty Map.empty

-- | Checks well-typedness of underlying theory.
typecheckMapping
  :: (ShowOrdN '[var, ty, sym, en, fk, att, en', fk', att'])
  => Mapping var ty sym en fk att en' fk' att'
  -> Err ()
typecheckMapping m =  typeOfMor $ mapToMor m

-- | Given @F@ checks that each @S |- p = q  ->  T |- F p = F q@.
validateMapping
  :: forall  var ty sym en fk att en' fk' att'
  . (ShowOrdN '[var, ty, sym, en, fk, att, en', fk', att'])
  => Mapping var ty sym en fk att en' fk' att'
  -> Err ()
validateMapping (m@(Mapping src' dst' ens' _ _)) = do
  _ <- mapM g (Set.toList $ path_eqs src')
  _ <- mapM f (Set.toList $ obs_eqs src')
  pure ()
  where
    f :: (en, EQ () ty sym en fk att Void Void) -> Err ()
    f (enx, EQ (l,r)) = let
      l'  = trans (mapToMor m) l
      r'  = trans (mapToMor m) r :: Term () ty sym en' fk' att' Void Void
      en' = fromJust $ Map.lookup enx ens'
      in if eq dst' en' (EQ (l', r'))
         then pure ()
         else Left $ show l ++ " = " ++ show r ++ " translates to " ++ show l' ++ " = " ++ show r' ++ " which is not provable"
    g :: (en, EQ () Void Void en fk Void Void Void) -> Err ()
    g (enx, EQ (l,r)) = let
      l' = trans' (mapToMor m) l
      r' = trans' (mapToMor m) r :: Term () Void Void en' fk' Void Void Void
      en'= fromJust $ Map.lookup enx ens'
      in if eq dst' en' (EQ (upp l', upp r'))
         then pure ()
         else Left $ show l ++ " = " ++ show r ++ " translates to " ++ show l' ++ " = " ++ show r' ++ " which is not provable"

-----------------------------------------------------------------------------------------------------------------
-- Syntax

data MappingExp where
  MappingVar     :: String                   -> MappingExp
  MappingId      :: SchemaExp                -> MappingExp
  MappingRaw     :: MappingExpRaw'           -> MappingExp
  MappingComp    :: MappingExp -> MappingExp -> MappingExp
  deriving (Eq, Show)

getOptionsMapping :: MappingExp -> [(String, String)]
getOptionsMapping x = case x of
  MappingVar  _                             -> []
  MappingId   _                             -> []
  MappingComp _ _                           -> []
  MappingRaw (MappingExpRaw' _ _ _ _ _ o _) -> o

instance Deps MappingExp where
  deps x = case x of
    MappingVar  v   -> [(v, MAPPING)]
    MappingId   s   -> deps s
    MappingComp f g -> deps f ++ deps g
    MappingRaw (MappingExpRaw' s t _ _ _ _ i) -> deps s ++ deps t ++ concatMap deps i

data MappingEx :: * where
  MappingEx
    :: forall var ty sym en fk att en' fk' att' . (ShowOrdTypeableN '[var, ty, sym, en, fk, att, en', fk', att'])
    => Mapping var ty sym en fk att en' fk' att'
    -> MappingEx

deriving instance Show MappingEx

instance NFData MappingEx where
  rnf (MappingEx x) = rnf x

-----------------------------------------------------------------------------------------------------------------
-- Operations

composeMapping
  :: (ShowOrdTypeableN '[var, ty, sym, en, fk, att, en', fk', att', en', fk', att', en'', fk'', att''])
  =>      Mapping var ty sym en  fk  att  en'  fk'  att'
  ->      Mapping var ty sym en' fk' att' en'' fk'' att''
  -> Err (Mapping var ty sym en  fk  att  en'' fk'' att'')
composeMapping (Mapping s t e f a) (m2@(Mapping s' t' e' _ _)) =
 if t == s'
 then let e'' = Map.fromList [ (k, fromJust $ Map.lookup v e') | (k, v) <- Map.toList e ]
          f'' = Map.fromList [ (k, trans'  (mapToMor m2) v)    | (k, v) <- Map.toList f ]
          a'' = Map.fromList [ (k, trans   (mapToMor m2) v)    | (k, v) <- Map.toList a ]
      in pure $ Mapping s t' e'' f'' a''
 else Left $ "Source and target schemas do not match: " ++ show t ++ " and " ++ show s'

-----------------------------------------------------------------------------------------------------------------
-- Literals

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

evalMappingRaw'
  :: forall var ty sym en fk att en' fk' att' . (ShowOrdTypeableN '[en, en'], Typeable sym, Ord fk, Typeable fk, Ord att, Typeable att, Ord fk', Typeable fk', Ord att', Typeable att')
  => Schema var ty sym en fk att -> Schema var ty sym en' fk' att'
  -> MappingExpRaw'
  -> [Mapping var ty sym en fk att en' fk' att']
  -> Err (Mapping var ty sym en fk att en' fk' att')
evalMappingRaw' src' dst' (MappingExpRaw' _ _ ens0 fks0 atts0 _ _) is = do
  ens1 <- conv'' ens0
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
                      Just x  -> return x
                      Nothing -> Left $ "No entity mapping for " ++ (show en)

    f _ [] = pure $ Map.empty
    f x ((att, Right l):ts) = do
      att' <- note ("Not a src attribute " ++ att) (cast att)
      att2 <- note ("Not a dst attribute " ++ att) (cast $ head $ reverse l)
      t'x  <- h ens' $ tail $ reverse l
      let t'  = Att att2 $ upp t'x
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
    g' _ _ _ _ = error "impossible"
    g :: String ->[fk']-> [att'] -> RawTerm -> Term () ty sym en' fk' att' Void Void
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

    conv'' :: forall tyx ty2x
      .  (Typeable tyx, Show tyx, Typeable ty2x, Show ty2x)
      => [(String, String)]
      -> Err [(ty2x, tyx)]
    conv'' [] = pure []
    conv'' ((ty2,ty):tl) = case (cast ty :: Maybe tyx) of
      Just ty' -> do
        x <- conv'' tl
        case cast ty2 :: Maybe ty2x of
          Just ty2' -> return $ (ty2', ty'):x
          Nothing   -> Left $ "Not in source schema/typeside: " ++ show ty2
      Nothing       -> Left $ "Not in target schema/typeside: " ++ show ty

evalMappingRaw
  :: (ShowOrdTypeableN '[var, ty, sym, en, fk, att, en', fk', att'])
  => Schema var ty sym en  fk  att
  -> Schema var ty sym en' fk' att'
  -> MappingExpRaw'
  -> [MappingEx]
  -> Err MappingEx
evalMappingRaw src' dst' t is = do
  (a :: [Mapping var ty sym en fk att en' fk' att']) <- g is
  r <- evalMappingRaw' src' dst' t a
  --l <- toOptions $ mapraw_options t
  pure $ MappingEx r
  where
    g :: forall var ty sym en fk att en' fk' att'. (Typeable var, Typeable ty, Typeable sym, Typeable en, Typeable fk, Typeable att, Typeable fk', Typeable en', Typeable att')
      => [MappingEx] -> Err [Mapping var ty sym en fk att en' fk' att']
    g [] = return []
    g ((MappingEx ts):r) = case cast ts of
      Nothing  -> Left "Bad import"
      Just ts' -> do { r'  <- g r ; return $ ts' : r' }





