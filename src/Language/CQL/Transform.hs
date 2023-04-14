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
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.CQL.Transform where

import           Control.DeepSeq
import           Data.Map                           (Map, mapWithKey)
import qualified Data.Map.Strict                    as Map
import           Data.Kind
import           Data.Maybe
import qualified Data.Set                           as Set
import           Data.Typeable
import           Data.Void
import           Language.CQL.Common
import           Language.CQL.Instance              as I
import qualified Language.CQL.Instance.Presentation as IP (Presentation(eqs, gens, sks), toCollage)
import           Language.CQL.Instance.Algebra      (Algebra(..), Carrier, nf, nf'', TalgGen(..))
import           Language.CQL.Mapping               as M hiding (toMorphism)
import           Language.CQL.Morphism              (Morphism(..), translate, translate')
import           Language.CQL.Morphism              as Morphism (typeOf)
import           Language.CQL.Options
import           Language.CQL.Query
import           Language.CQL.Schema                as S
import           Language.CQL.Term
import           Prelude                            hiding (EQ)


-- | Map from one 'Instance' to another of the same 'Schema'.
data Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  = Transform
  { srcT :: Instance var ty sym en fk att gen sk x y
  , dstT :: Instance var ty sym en fk att gen' sk' x' y'
  , gens :: Map gen (Term Void Void Void en fk Void gen' Void)
  , sks  :: Map sk  (Term Void ty   sym  en fk att  gen' sk')
  }

instance TyMap NFData '[var, ty, sym, en, fk, att, gen, sk, x, y, gen', sk', x', y']
  => NFData (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  rnf (Transform s t g a) = deepseq s $ deepseq t $ deepseq g $ rnf a

instance TyMap Show '[var, ty, sym, en, fk, att, gen, sk, x, y, gen', sk', x', y']
  => Show (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  show (Transform _ _ gens' sks') =
    "transform {" ++
    "generators\n\t"  ++ intercalate "\n\t" ens'' ++ "\n" ++
    "nulls\n\t" ++ intercalate "\n\t" fks'' ++
    "}"
   where ens'' = Prelude.map (\(s,t) -> show s ++ " -> " ++ show t) $ Map.toList gens'
         fks'' = Prelude.map (\(k,s) -> show k ++ " -> " ++ show s) $ Map.toList sks'

instance TyMap Eq '[var, ty, sym, en, fk, att, gen, sk, x, y, gen', sk', x', y']
  => Eq (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  (==) (Transform s1 s2 gens' sks') (Transform s1' s2' gens'' sks'')
    = (s1 == s1') && (s2 == s2') && (gens' == gens'') && (sks' == sks'')

tGens :: Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> Map gen (Term Void Void Void en fk Void gen' Void)
tGens = gens

tSks :: Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> Map sk  (Term Void ty   sym  en fk att  gen' sk')
tSks = sks

typecheckTransform
  :: (MultiTyMap '[Show, Ord, Typeable, NFData] '[sym, en, fk, att], MultiTyMap '[Show, Ord, NFData] '[var, ty, gen, sk, x, y, gen', sk', x', y'])
  => Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  -> Err ()
typecheckTransform m = Morphism.typeOf $ toMorphism m

validateTransform
  :: forall var ty sym en fk att gen sk x y gen' sk' x' y' -- need forall
  . (MultiTyMap '[Show, Ord, Typeable, NFData] '[sym, en, fk, att], MultiTyMap '[Show, Ord, NFData] '[var, ty, gen, sk, x, y, gen', sk', x', y'])
  => Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  -> Err ()
validateTransform m@(Transform src' dst' _ _) =
  mapM_ f (Set.toList $ IP.eqs $ pres src')
  where
    f :: (EQ Void ty sym en fk att gen sk) -> Err () -- need type signature
    f (EQ (l, r)) = let
      l' = translate (toMorphism m) l
      r' = translate (toMorphism m) r :: Term Void ty sym en fk att gen' sk'
      in if dp dst' (EQ (l',   r'))
         then pure ()
         else Left $ show l ++ " = " ++ show r ++ " translates to " ++ show l' ++ " = " ++ show r' ++ " which is not provable"

toMorphism
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, gen, sk, en', fk', att', gen', sk'])
  => Transform var ty sym en' fk' att' gen sk x1  y1       gen' sk' x2 y2
  -> Morphism  var ty sym en' fk' att' gen sk en' fk' att' gen' sk'
toMorphism (Transform src' dst' gens' sks') =
  Morphism (IP.toCollage (I.schema src') (pres src'))
           (IP.toCollage (I.schema src') (pres dst'))
           ens0 fks0 atts0 gens' sks'
  where
    ens0  = Map.fromSet id                          (S.ens  $ I.schema src')
    fks0  = mapWithKey  (\fk  _ -> Fk  fk (Var ())) (S.fks  $ I.schema src')
    atts0 = mapWithKey  (\fk  _ -> Att fk (Var ())) (S.atts $ I.schema src')

------------------------------------------------------------------------------------------------------------
-- Expressions

data TransformEx :: Type where
  TransformEx
    :: forall var ty sym en fk att gen sk x y gen' sk' x' y'
    . (MultiTyMap '[Show, Ord, Typeable, NFData] '[var, ty, sym, en, fk, att, gen, sk, x, y, gen', sk', x', y'])
    => Transform var ty sym en fk att gen sk x y gen' sk' x' y'
    -> TransformEx

instance NFData TransformEx where
  rnf (TransformEx x) = rnf x

deriving stock instance Show TransformEx

data TransformExp  where
  TransformComp             :: TransformExp              -> TransformExp       -> TransformExp
  TransformVar              :: String                                          -> TransformExp
  TransformId               :: InstanceExp                                     -> TransformExp
  TransformSigmaDeltaUnit   :: MappingExp -> InstanceExp -> [(String,String)]  -> TransformExp
  TransformSigmaDeltaCoUnit :: MappingExp -> InstanceExp -> [(String,String)]  -> TransformExp
  TransformDeltaPiUnit      :: MappingExp                                      -> TransformExp
  TransformDeltaPiCoUnit    :: MappingExp                                      -> TransformExp
  TransformQueryUnit        :: QueryExp                                        -> TransformExp
  TransformQueryCoUnit      :: MappingExp                                      -> TransformExp
  TransformDelta            :: MappingExp -> TransformExp -> [(String,String)] -> TransformExp
  TransformSigma            :: MappingExp -> TransformExp -> [(String,String)] -> TransformExp
  TransformPi               :: MappingExp -> TransformExp                      -> TransformExp
  TransformCoEval           :: QueryExp   -> TransformExp                      -> TransformExp
  TransformEval             :: QueryExp   -> TransformExp                      -> TransformExp
  TransformRaw              :: TransExpRaw'                                    -> TransformExp
 deriving stock Show

instance Deps TransformExp where
  deps x = case x of
    TransformVar                        v -> [(v,TRANSFORM)]
    TransformId                       i   -> deps i
    TransformSigmaDeltaUnit         f i _ -> deps f ++ deps i
    TransformSigmaDeltaCoUnit       f i _ -> deps f ++ deps i
    TransformDelta                  f i _ -> deps f ++ deps i
    TransformSigma                  f i _ -> deps f ++ deps i
    TransformComp                   f g   -> deps f ++ deps g
    TransformRaw (TransExpRaw' s t _ _ i) -> deps s ++ deps t ++ concatMap deps i
    _                                     -> error "other transforms"

getOptionsTransform :: TransformExp -> [(String, String)]
getOptionsTransform x = case x of
  TransformVar _                        -> []
  TransformId _                         -> []
  TransformSigmaDeltaUnit _ _ o         -> o
  TransformSigmaDeltaCoUnit _ _ o       -> o
  TransformDelta _ _ o                  -> o
  TransformSigma _ _ o                  -> o
  TransformRaw (TransExpRaw' _ _ _ o _) -> o
  TransformComp _ _                     -> []
  _                                     -> error "other transforms"

---------------------------------------------------------------------------------------------------------
-- Evaluation

composeTransform
  :: (MultiTyMap '[Show, Ord, Typeable, NFData] '[var, ty, sym, en, fk, att, gen, sk, x, y, gen', sk', x', y', gen'', sk'', x'', y''])
  =>      Transform var ty sym en fk att gen  sk  x  y  gen'  sk'  x'  y'
  ->      Transform var ty sym en fk att gen' sk' x' y' gen'' sk'' x'' y''
  -> Err (Transform var ty sym en fk att gen  sk  x  y  gen'' sk'' x'' y'')
composeTransform (Transform s t f a) m2@(Transform s' t' _ _)
  | t == s'   = pure $ Transform s t' f'' a''
  | otherwise = Left $ "Source and target instances do not match: " ++ show t ++ " and " ++ show s'
  where
    f'' = Map.fromList [ (k, translate' (toMorphism m2) v) | (k, v) <- Map.toList f ]
    a'' = Map.fromList [ (k, translate  (toMorphism m2) v) | (k, v) <- Map.toList a ]

evalSigmaTrans
  :: (MultiTyMap '[Show, Ord, Typeable, NFData] '[var, ty, sym, en, fk, att, gen, sk, en', fk', att', gen', sk', x', y'])
  => Mapping var ty sym en fk att en' fk' att'
  -> Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  -> Options
  -> Err (Transform var ty sym en' fk' att' gen sk (Carrier en' fk' gen) (TalgGen en' fk' att' gen sk) gen' sk' (Carrier en' fk' gen') (TalgGen en' fk' att' gen' sk'))
evalSigmaTrans f (Transform src0 dst0 gens' sks') o = do
  src' <- evalSigmaInst f src0 o
  dst' <- evalSigmaInst f dst0 o
  pure $ Transform src' dst' gens'' sks''
  where
    gens'' = changeEn' (M.fks f) (M.atts f) <$> gens'
    sks''  = changeEn  (M.fks f) (M.atts f) <$> sks'

evalDeltaSigmaUnit
  :: forall var ty sym en fk att gen sk x y en' fk' att' . (MultiTyMap '[Show, Ord, Typeable, NFData] '[var, ty, sym, en, fk, att, en', fk', att', gen, sk, x, y])
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en fk att gen sk x y
  -> Options
  -> Err (Transform var ty sym en fk att gen sk x y (en, Carrier en' fk' gen) (TalgGen en' fk' att' gen sk) (en,Carrier en' fk' gen) (TalgGen en' fk' att' gen sk))
evalDeltaSigmaUnit m i o = do
  j <- evalSigmaInst m i o
  k <- evalDeltaInst m j o
  pure $ Transform i k (mapWithKey (f j) $ IP.gens $ pres i)
                       (mapWithKey (g j) $ IP.sks  $ pres i)
  where
    f j gen en' = Gen (en', nf   (algebra j) $ Gen gen)
    g j sk  _   = upp $     nf'' (algebra j) $ Sk  sk

evalDeltaSigmaCoUnit
  :: forall var ty sym en fk att gen sk x y en' fk' att'. (MultiTyMap '[Show, Ord, Typeable, NFData] '[var, ty, sym, en, fk, att, gen, sk, x, y, en', fk', att'])
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en' fk' att' gen sk x y
  -> Options
  -> Err (Transform var ty sym en' fk' att' (en, x) y (Carrier en' fk' (en, x)) (TalgGen en' fk' att' (en, x) y) gen sk x y)
evalDeltaSigmaCoUnit m i o = do
  j <- evalDeltaInst m i o
  k <- evalSigmaInst m j o
  return $ Transform k i (Map.fromList $ fmap (f j) $ Map.toList $ IP.gens $ pres k) $ (Map.fromList $ fmap (g j) $ Map.toList $ IP.sks $ pres k)
  where
    f _ ((en', x), _) = ((en', x), repr  (algebra i) x )
    g _ (sk      , _) = (sk      , repr' (algebra i) sk)

evalDeltaTrans
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, en', fk', att', gen, sk, x, y, gen', sk', x', y'])
  => Mapping var ty sym en fk att en' fk' att'
  -> Transform var ty sym en' fk' att' gen sk x y gen' sk' x' y'
  -> Options
  -> Err (Transform var ty sym en fk att (en,x) y (en,x) y (en,x') y' (en,x') y')
evalDeltaTrans m h o = do
  i <- evalDeltaInst m (srcT h) o
  j <- evalDeltaInst m (dstT h) o
  pure $ Transform i j (gens' i) (sks' i)
  where
    gens' i = mapWithKey (\(_,x) en' -> Gen (en', nf   (algebra $ dstT h) $ translate' (toMorphism h) $ repr  (algebra $ srcT h) x)) $ IP.gens $ pres i
    sks'  i = mapWithKey (\y     _   -> upp  $    nf'' (algebra $ dstT h) $ translate  (toMorphism h) $ repr' (algebra $ srcT h) y)  $ IP.sks  $ pres i

---------------------------------------------------------------------------------------------------------
-- Raw literals

data TransExpRaw'
  = TransExpRaw'
  { transraw_src     :: InstanceExp
  , transraw_dst     :: InstanceExp
  , transraw_gens    :: [(String, RawTerm)]
  , transraw_options :: [(String, String)]
  , transraw_imports :: [TransformExp]
} deriving stock Show

-- | Evaluates a literal into a transform.
evalTransformRaw
  :: forall var ty sym en fk att gen sk x y gen' sk' x' y'
  .  (MultiTyMap '[Show, Ord, Typeable, NFData] '[var, ty, sym, en, fk, att, gen, sk, x, y, gen', sk', x', y'])
  => Instance var ty sym en fk att gen  sk  x  y
  -> Instance var ty sym en fk att gen' sk' x' y'
  -> TransExpRaw'
  -> [TransformEx]
  -> Err TransformEx
evalTransformRaw s t h is = do
  (a :: [Transform var ty sym en fk att gen sk x y gen' sk' x' y']) <- doImports is
  r <- evalTransformRaw' s t h a
--l <- toOptions $ mapraw_options t
  pure $ TransformEx r
  where
    doImports [] = return []
    doImports ((TransformEx ts):r) = case cast ts of
      Nothing  -> Left "Bad import"
      Just ts' -> do { r'  <- doImports r ; return $ ts' : r' }

evalTransformRaw'
  :: forall var ty sym en fk att gen sk x y gen' sk' x' y'
  .  (MultiTyMap '[Ord, Typeable] '[fk, att, gen, sk, gen', sk'], Typeable sym)
  => Instance var ty sym en fk att gen  sk  x  y
  -> Instance var ty sym en fk att gen' sk' x' y'
  -> TransExpRaw'
  -> [Transform var ty sym en fk att gen sk x y gen' sk' x' y']
  -> Err (Transform var ty sym en fk att gen sk x y gen' sk' x' y')
evalTransformRaw' src' dst' (TransExpRaw' _ _ sec _ _) is = do
  theseGens <- evalGens gens0
  theseSks  <- evalSks sks0
  return $ Transform src' dst' (addImportGens theseGens) $ addImportSks theseSks
  where
    addImportGens x = foldr (Map.union . tGens) x is
    addImportSks  y = foldr (Map.union . tSks)  y is

    gens'' = IP.gens $ pres src'
    sks''  = IP.sks  $ pres src'
    gens'  = IP.gens $ pres dst'
    sks'   = IP.sks  $ pres dst'
    gens0  = filter (\(x,_) -> x `member'` gens'') sec
    sks0   = filter (\(x,_) -> x `member'` sks'' ) sec

    evalGens []             = pure Map.empty
    evalGens  ((gen, t):ts) = do
      t'   <- evalPath t
      rest <- evalGens ts
      gen' <- note ("Not a generator: " ++ gen) (cast gen)
      pure $ Map.insert gen' t' rest

    evalSks []             = pure $ Map.empty
    evalSks  ((gen, t):ts) = do
      t'   <- evalTerm t
      rest <- evalSks ts
      gen' <- note ("Not a null: " ++ gen) (cast gen)
      pure $ Map.insert gen' t' rest

    evalTerm ::  RawTerm -> Err (Term Void ty sym en fk att gen' sk')
    evalTerm (RawApp x [])     | x `member'` gens''                     =
      pure $ Gen $ fromJust $ cast x
    evalTerm (RawApp x [])     | x `member'` sks'                       =
      pure $ Sk  $ fromJust $ cast x
    evalTerm (RawApp x (a:[])) | x `member'` (sch_fks $ I.schema dst')  = do
      a' <- evalTerm a
      case cast x of
        Just x'2 -> return $ Fk x'2 a'
        Nothing  -> undefined
    evalTerm (RawApp x (a:[])) | x `member'` (sch_atts $ I.schema dst') = do
      a' <- evalTerm a
      case cast x of
        Just x'2 -> return $ Att x'2 a'
        Nothing  -> undefined
    evalTerm  (RawApp v l)                                              = do
      l' <- mapM evalTerm l
      case cast v :: Maybe sym of
        Just x  -> pure $ Sym x l'
        Nothing -> undefined

    evalPath :: RawTerm -> Err (Term Void Void Void en fk Void gen' Void)
    evalPath (RawApp x [])     | x `member'` gens'                      =
      pure $ Gen $ fromJust $ cast x
    evalPath (RawApp x (a:[])) | x `member'` (sch_fks $ I.schema dst')  = do
      a' <- evalPath a
      case cast x of
        Just x'2 -> return $ Fk x'2 a'
        Nothing  -> undefined
    evalPath _                                                          = undefined
