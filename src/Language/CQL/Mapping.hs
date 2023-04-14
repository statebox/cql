{-
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `statebox/cql`, the categorical query language.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
-}
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
{-# LANGUAGE DerivingStrategies #-}

module Language.CQL.Mapping where

import           Control.DeepSeq
import           Data.Map.Strict       as Map
import           Data.Maybe
import qualified Data.Set              as Set
import           Data.Typeable
import           Data.Kind
import           Data.Void
import           Language.CQL.Common
import           Language.CQL.Morphism (Morphism(..), translate, translate')
import           Language.CQL.Morphism as Morphism (typeOf)
import           Language.CQL.Schema   as Schema
import           Language.CQL.Term
import           Prelude               hiding (EQ)

-- | Morphism of schemas.
data Mapping var ty sym en fk att en' fk' att'
  = Mapping
  { src  :: Schema var ty sym en  fk  att
  , dst  :: Schema var ty sym en' fk' att'

  , ens  :: Map en  en'
  , fks  :: Map fk  (Term () Void Void en' fk' Void Void Void)
  , atts :: Map att (Term () ty   sym  en' fk' att' Void Void)
  }

instance TyMap NFData '[var, ty, sym, en, fk, att, en', fk', att']
  => NFData (Mapping var ty sym en fk att en' fk' att') where
  rnf (Mapping s t e f a) = deepseq s $ deepseq t $ deepseq e $ deepseq f $ rnf a

instance TyMap Show '[var, ty, sym, en, fk, att, en', fk', att']
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

instance TyMap Eq '[var, ty, sym, en, fk, att, en', fk', att']
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

toMorphism
  :: MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, en', fk', att']
  => Mapping var ty sym en fk att en' fk' att'
  -> Morphism var ty sym en fk att Void Void en' fk' att' Void Void
toMorphism (Mapping src' dst' ens' fks' atts') = Morphism (Schema.toCollage src') (Schema.toCollage dst') ens' fks' atts' Map.empty Map.empty

-- | Checks well-typedness of underlying theory.
typecheckMapping
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty], MultiTyMap '[Show, Ord, Typeable, NFData] '[sym, en, fk, att, en', fk', att'])
  => Mapping var ty sym en fk att en' fk' att'
  -> Err ()
typecheckMapping m = Morphism.typeOf $ toMorphism m

-- | Given @F@ checks that each @S |- p = q  ->  T |- F p = F q@.
validateMapping
  :: forall  var ty sym en fk att en' fk' att'
  . (MultiTyMap '[Show, Ord, NFData] '[var, ty], MultiTyMap '[Show, Ord, Typeable, NFData] '[sym, en, fk, att, en', fk', att'])
  => Mapping var ty sym en fk att en' fk' att'
  -> Err ()
validateMapping m@(Mapping src' dst' ens' _ _) = do
  mapM_ validatePathEq (Set.toList $ path_eqs src')
  mapM_ validateObsEq  (Set.toList $ obs_eqs  src')
  where
    validateObsEq :: (en, EQ () ty sym en fk att Void Void) -> Err ()
    validateObsEq (enx, EQ (l,r)) = let
      l'  = translate (toMorphism m) l
      r'  = translate (toMorphism m) r :: Term () ty sym en' fk' att' Void Void
      en' = ens' ! enx
      in if eq dst' en' (EQ (l', r'))
         then pure ()
         else Left $ show l ++ " = " ++ show r ++ " translates to " ++ show l' ++ " = " ++ show r' ++ " which is not provable"
    validatePathEq :: (en, EQ () Void Void en fk Void Void Void) -> Err ()
    validatePathEq (enx, EQ (l,r)) = let
      l'  = translate' (toMorphism m) l
      r'  = translate' (toMorphism m) r :: Term () Void Void en' fk' Void Void Void
      en' = ens' ! enx
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
  deriving stock (Eq, Show)

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

data MappingEx :: Type where
  MappingEx
    :: forall var ty sym en fk att en' fk' att' . (MultiTyMap '[Show, Ord, Typeable, NFData] '[var, ty, sym, en, fk, att, en', fk', att'])
    => Mapping var ty sym en fk att en' fk' att'
    -> MappingEx

deriving stock instance Show MappingEx

instance NFData MappingEx where
  rnf (MappingEx x) = rnf x

-----------------------------------------------------------------------------------------------------------------
-- Operations

-- | Compose two mappings.
composeMapping
  :: (MultiTyMap '[Show, Ord, Typeable, NFData] '[var, ty, sym, en, fk, att, en', fk', att', en', fk', att', en'', fk'', att''])
  =>      Mapping var ty sym en  fk  att  en'  fk'  att'
  ->      Mapping var ty sym en' fk' att' en'' fk'' att''
  -> Err (Mapping var ty sym en  fk  att  en'' fk'' att'')
composeMapping (Mapping s t e f a) m2@(Mapping s' t' e' _ _) =
  if t == s'
  then let e'' = Map.fromList [ (k, e' ! v)                       | (k, v) <- Map.toList e ]
           f'' = Map.fromList [ (k, translate' (toMorphism m2) v) | (k, v) <- Map.toList f ]
           a'' = Map.fromList [ (k, translate  (toMorphism m2) v) | (k, v) <- Map.toList a ]
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
} deriving stock (Eq, Show)

-- | Does the hard work of @evalMappingRaw@.
evalMappingRaw'
  :: forall var ty sym en fk att en' fk' att' . (MultiTyMap '[Show, Ord, Typeable, NFData] '[sym, en, fk, att, en', fk', att'])
  => Schema var ty sym en fk att -> Schema var ty sym en' fk' att'
  -> MappingExpRaw'
  -> [Mapping var ty sym en fk att en' fk' att']
  -> Err (Mapping var ty sym en fk att en' fk' att')
evalMappingRaw' src' dst' (MappingExpRaw' _ _ ens0 fks0 atts0 _ _) is = do
  ens1 <- multiCast ens0
  ens2 <- toMapSafely ens1
  theFks  <- evalFks  fks0
  theAtts <- evalAtts (allEns ens2) atts0
  return $ Mapping src' dst' (allEns ens2) (mergeMaps $ theFks : fmap getFks is) (mergeMaps $ theAtts : fmap getAtts is)
  where
    allEns ensX = Map.fromList $ Map.toList ensX ++ concatMap (Map.toList . getEns) is
    keys'  = fmap fst
    fks'   = Map.toList $ Schema.fks dst'
    ens'   = Set.toList $ Schema.ens dst'
    atts'  = Map.toList $ Schema.atts dst'
    transE ens2 en = case Map.lookup en ens2 of
      Just x  -> return x
      Nothing -> Left $ "No entity mapping for " ++ show en

    evalAtts _ [] = pure $ Map.empty
    evalAtts x ((att, Right l):ts) = do
      att' <- note ("Not a src attribute " ++ att) (cast att)
      att2 <- note ("Not a dst attribute " ++ att) (cast $ last l)
      t'x  <- inferPath ens' $ tail $ reverse l
      let t'  = Att att2 $ upp t'x
      rest <- evalAtts x ts
      pure $ Map.insert att' t' rest
    evalAtts x ((att, Left (v, t2, t)):ts) = do
      att' <- note ("Not an attribute " ++ att) (cast att)
      let t' = inferTerm v (keys' fks') (keys' atts') t
      rest <- evalAtts x ts
      let ret = pure $ Map.insert att' t' rest
          (s,_) = Schema.atts src' ! att'
      s' <- transE x s
      case t2 of
        Nothing -> ret
        Just t3 -> case cast t3 of
          Nothing -> Left $ "Not an entity: " ++ t3
          Just t4 -> if t4 == s'
            then ret
            else Left $ "Type mismatch: " ++ show s' ++ " and " ++ show t3

    -- :: String ->[String]-> [String] -> RawTerm-> Term () Void Void en Fk Void  Void Void
    inferTerm' v _ _ (RawApp x []) | v == x = Var ()
    inferTerm' v fks'' atts'' (RawApp x (a:[])) | elem' x fks'' = Fk (fromJust $ cast x) $ inferTerm' v fks'' atts'' a
    inferTerm' _ _ _ _ = error "impossible"

    --inferTerm :: Typeable sym => String ->[fk']-> [att'] -> RawTerm -> Term () ty sym en' fk' att' Void Void
    inferTerm v _ _ (RawApp x []) | v == x = Var ()
    inferTerm v fks'' atts'' (RawApp x (a:[])) | elem' x fks''  = Fk  (fromJust $ cast x) $ inferTerm' v fks'' atts'' a
    inferTerm v fks'' atts'' (RawApp x (a:[])) | elem' x atts'' = Att (fromJust $ cast x) $ inferTerm' v fks'' atts'' a
    inferTerm u fks'' atts'' (RawApp v l) = let l' = Prelude.map (inferTerm u fks'' atts'') l in
      case cast v of
        Just x  -> Sym x l'
        Nothing -> error "impossible until complex typesides"

    -- :: [en'] -> [String] -> Err (Term () Void Void en' fk' Void Void Void)
    inferPath ens'' (s:ex) | elem' s ens'' = inferPath ens'' ex
    inferPath ens'' (s:ex) | elem' s (keys' fks') = do { h' <- inferPath ens'' ex ; return $ Fk (fromJust $ cast s) h' }
                 | otherwise = Left $ "Not a target fk: " ++ s
    inferPath _ [] = return $ Var ()

    --  :: [(String, [String])] -> Err (Map fk (Term () Void Void en' fk' Void Void Void))
    evalFks []            = pure Map.empty
    evalFks ((fk,p):eqs') = do
      p' <- inferPath ens' $ reverse p
      --    _ <- findEn ens' fks' p
      rest <- evalFks eqs'
      fk' <- note ("Not a src fk: " ++ fk) (cast fk)
      pure $ Map.insert fk' p' rest

    multiCast :: forall tyx ty2x
      .  (Typeable tyx, Show tyx, Typeable ty2x, Show ty2x)
      => [(String, String)]
      -> Err [(ty2x, tyx)]
    multiCast [] = pure []
    multiCast ((ty2,ty):tl) = case (cast ty :: Maybe tyx) of
      Just ty' -> do
        x <- multiCast tl
        case cast ty2 :: Maybe ty2x of
          Just ty2' -> return $ (ty2', ty'):x
          Nothing   -> Left $ "Not in source schema/typeside: " ++ show ty2
      Nothing       -> Left $ "Not in target schema/typeside: " ++ show ty

-- | Evaluates a literal into a mapping.  Does not typecheck or validate.
evalMappingRaw
  :: (MultiTyMap '[Show, Ord, Typeable, NFData] '[var, ty, sym, en, fk, att, en', fk', att'])
  => Schema var ty sym en  fk  att
  -> Schema var ty sym en' fk' att'
  -> MappingExpRaw'
  -> [MappingEx]
  -> Err MappingEx
evalMappingRaw src' dst' t is = do
  (a :: [Mapping var ty sym en fk att en' fk' att']) <- doImports is
  r <- evalMappingRaw' src' dst' t a
  --l <- toOptions $ mapraw_options t
  pure $ MappingEx r
  where
    -- g :: forall var ty sym en fk att en' fk' att'. TyMap Typeable '[var, ty, sym, en, fk, att, fk', en', att']
    --   => [MappingEx] -> Err [Mapping var ty sym en fk att en' fk' att']
    doImports [] = return []
    doImports (MappingEx ts : r) = case cast ts of
      Nothing  -> Left "Bad import"
      Just ts' -> do { r'  <- doImports r ; return $ ts' : r' }
