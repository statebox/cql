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

module Language.Transform where

import           Data.Map          (Map, mapWithKey)
import qualified Data.Map.Strict   as Map
import           Data.Maybe
import qualified Data.Set          as Set
import           Data.Typeable
import           Data.Void
import           Language.Common
import           Language.Instance as I
import           Language.Mapping  as M
import           Language.Options
import           Language.Query
import           Language.Schema   as S
import           Language.Term
import           Prelude           hiding (EQ)
import           Control.DeepSeq


-- | Map from one 'Instance' to another of the same 'Schema'.
data Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  = Transform
  { srcT :: Instance var ty sym en fk att gen sk x y
  , dstT :: Instance var ty sym en fk att gen' sk' x' y'
  , gens :: Map gen (Term Void Void Void en fk Void gen' Void)
  , sks  :: Map sk  (Term Void ty   sym  en fk att  gen' sk')
  }

instance (NFData var, NFData ty, NFData sym, NFData en, NFData fk, NFData att, NFData gen, NFData sk, NFData x, NFData y, NFData gen', NFData sk', NFData x', NFData y')
  => NFData (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  rnf (Transform s t g a) = deepseq s $ deepseq t $ deepseq g $ rnf a

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk,
          Show x, Show y, Show gen', Show sk', Show x', Show y')
  => Show (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  show (Transform _ _ gens' sks') =
    "transform {" ++
    "generators\n\t"  ++ intercalate "\n\t" ens'' ++ "\n" ++
    "nulls\n\t" ++ intercalate "\n\t" fks'' ++
    "}"
   where ens'' = Prelude.map (\(s,t) -> show s ++ " -> " ++ show t) $ Map.toList gens'
         fks'' = Prelude.map (\(k,s) -> show k ++ " -> " ++ show s) $ Map.toList sks'

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Eq x, Eq y, Eq gen', Eq sk', Eq x', Eq y')
  => Eq (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  (==) (Transform s1 s2 gens' sks') (Transform s1' s2' gens'' sks'')
    = (s1 == s1') && (s2 == s2') && (gens' == gens'') && (sks' == sks'')

tGens :: Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> Map gen (Term Void Void Void en fk Void gen' Void)
tGens = gens

tSks :: Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> Map sk  (Term Void ty   sym  en fk att  gen' sk')
tSks = sks

typecheckTransform
  :: (ShowOrdTypeableN '[sym, en, fk, att], ShowOrdN '[var, ty, gen, sk, x, y, gen', sk', x', y'])
  => Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  -> Err ()
typecheckTransform m = typeOfMor $ transToMor m

validateTransform
  :: forall var ty sym en fk att gen sk x y gen' sk' x' y' -- need forall
  . (ShowOrdTypeableN '[sym, en, fk, att], ShowOrdN '[var, ty, gen, sk, x, y, gen', sk', x', y'])
  => Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  -> Err ()
validateTransform (m@(Transform src' dst' _ _)) = do
  _ <- mapM_ f (Set.toList $ eqs $ pres src')
  pure ()
  where
    f :: (EQ Void ty sym en fk att gen sk) -> Err () -- need type signature
    f (EQ (l, r)) = let
      l' = trans (transToMor m) l
      r' = trans (transToMor m) r :: Term Void ty sym en fk att gen' sk'
      in if dp dst' (EQ (l',   r'))
         then pure ()
         else Left $ show l ++ " = " ++ show r ++ " translates to " ++ show l' ++ " = " ++ show r' ++ " which is not provable"

transToMor
  :: (ShowOrdN '[var, ty, sym, gen, sk, en', fk', att', gen', sk'])
  => Transform var ty sym en' fk' att' gen sk x1  y1       gen' sk' x2 y2
  -> Morphism  var ty sym en' fk' att' gen sk en' fk' att' gen' sk'
transToMor (Transform src' dst' gens' sks') =
  Morphism (presToCol (I.schema src') (pres src'))
           (presToCol (I.schema src') (pres dst'))
           ens0 fks0 atts0 gens' sks'
  where
    ens0  = Map.fromSet (\en0   -> en0            ) (S.ens  $ I.schema src')
    fks0  = mapWithKey  (\fk  _ -> Fk  fk (Var ())) (S.fks  $ I.schema src')
    atts0 = mapWithKey  (\fk  _ -> Att fk (Var ())) (S.atts $ I.schema src')

------------------------------------------------------------------------------------------------------------
-- Expressions

data TransformEx :: * where
  TransformEx
    :: forall var ty sym en fk att gen sk x y gen' sk' x' y'
    . (ShowOrdTypeableN '[var, ty, sym, en, fk, att, gen, sk, x, y, gen', sk', x', y'])
    => Transform var ty sym en fk att gen sk x y gen' sk' x' y'
    -> TransformEx

instance NFData TransformEx where
  rnf (TransformEx x) = rnf x

deriving instance Show TransformEx

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
 deriving Show

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
  TransformVar _ -> []
  TransformId _ -> []
  TransformSigmaDeltaUnit _ _ o -> o
  TransformSigmaDeltaCoUnit _ _ o -> o
  TransformDelta _ _ o -> o
  TransformSigma _ _ o -> o
  TransformRaw (TransExpRaw' _ _ _ o _) -> o
  TransformComp _ _ -> []
  _ -> error "other transforms"

---------------------------------------------------------------------------------------------------------
-- Evaluation

composeTransform
  :: (ShowOrdTypeableN '[var, ty, sym, en, fk, att, gen, sk, x, y, gen', sk', x', y', gen'', sk'', x'', y''])
  =>      Transform var ty sym en fk att gen  sk  x  y  gen'  sk'  x'  y'
  ->      Transform var ty sym en fk att gen' sk' x' y' gen'' sk'' x'' y''
  -> Err (Transform var ty sym en fk att gen  sk  x  y  gen'' sk'' x'' y'')
composeTransform (Transform s t f a) m2@(Transform s' t' _ _)
  | t == s'   = pure $ Transform s t' f'' a''
  | otherwise = Left $ "Source and target instances do not match: " ++ show t ++ " and " ++ show s'
  where
    f'' = Map.fromList [ (k, trans' (transToMor m2) v) | (k, v) <- Map.toList f ]
    a'' = Map.fromList [ (k, trans  (transToMor m2) v) | (k, v) <- Map.toList a ]

evalSigmaTrans
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk, en', fk', att', gen', sk', x', y'], Eq x, Eq y, Eq en')
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
  :: forall var ty sym en fk att gen sk x y en' fk' att' . (ShowOrdN '[var, ty, sym, en, fk, att, en', fk', att', gen, sk, x, y],  Eq x, Eq y, Eq en')
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en fk att gen sk x y
  -> Options
  -> Err (Transform var ty sym en fk att gen sk x y (en, Carrier en' fk' gen) (TalgGen en' fk' att' gen sk) (en,Carrier en' fk' gen) (TalgGen en' fk' att' gen sk))
evalDeltaSigmaUnit m i o = do
  j <- evalSigmaInst m i o
  k <- evalDeltaInst m j o
  pure $ Transform i k (mapWithKey (f j) $ I.gens $ pres i)
                       (mapWithKey (g j) $ I.sks  $ pres i)
  where
    f j gen en' = Gen (en', nf   (algebra j) $ Gen gen)
    g j sk  _   = upp $     nf'' (algebra j) $ Sk  sk

evalDeltaSigmaCoUnit
  :: forall var ty sym en fk att gen sk x y en' fk' att'. (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk, x, y, en', fk', att'], Eq x, Eq y, Eq en')
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en' fk' att' gen sk x y
  -> Options
  -> Err (Transform var ty sym en' fk' att' (en, x) y (Carrier en' fk' (en, x)) (TalgGen en' fk' att' (en, x) y) gen sk x y)
evalDeltaSigmaCoUnit m i o = do
  j <- evalDeltaInst m i o
  k <- evalSigmaInst m j o
  return $ Transform k i (Map.fromList $ fmap (f j) $ Map.toList $ I.gens $ pres k) $ (Map.fromList $ fmap (g j) $ Map.toList $ I.sks $ pres k)
  where
    f _ ((en', x), _) = ((en', x), repr  (algebra i) x )
    g _ (sk      , _) = (sk      , repr' (algebra i) sk)

evalDeltaTrans
  :: (ShowOrdN '[var, ty, sym, en, fk, att, en', fk', att', gen, sk, x, y, gen', sk', x', y'])
  => Mapping var ty sym en fk att en' fk' att'
  -> Transform var ty sym en' fk' att' gen sk x y gen' sk' x' y'
  -> Options
  -> Err (Transform var ty sym en fk att (en,x) y (en,x) y (en,x') y' (en,x') y')
evalDeltaTrans m h o = do
  i <- evalDeltaInst m (srcT h) o
  j <- evalDeltaInst m (dstT h) o
  pure $ Transform i j (gens' i) (sks' i)
  where
    gens' i = mapWithKey (\(_,x) en' -> Gen (en', nf   (algebra $ dstT h) $ trans' (transToMor h) $ repr  (algebra $ srcT h) x)) $ I.gens $ pres i
    sks'  i = mapWithKey (\y     _   -> upp  $    nf'' (algebra $ dstT h) $ trans  (transToMor h) $ repr' (algebra $ srcT h) y)  $ I.sks  $ pres i

---------------------------------------------------------------------------------------------------------
-- Raw literals

data TransExpRaw'
  = TransExpRaw'
  { transraw_src     :: InstanceExp
  , transraw_dst     :: InstanceExp
  , transraw_gens    :: [(String, RawTerm)]
  , transraw_options :: [(String, String)]
  , transraw_imports :: [TransformExp]
} deriving Show

-- | Evaluates a literal into a transform.
evalTransformRaw
  :: forall var ty sym en fk att gen sk x y gen' sk' x' y'
  .  (ShowOrdTypeableN '[var, ty, sym, en, fk, att, gen, sk, x, y, gen', sk', x', y'])
  => Instance var ty sym en fk att gen  sk  x  y
  -> Instance var ty sym en fk att gen' sk' x' y'
  -> TransExpRaw'
  -> [TransformEx]
  -> Err (TransformEx)
evalTransformRaw s t h is = do
  (a :: [Transform var ty sym en fk att gen sk x y gen' sk' x' y']) <- doImports is
  r <- evalTransformRaw' s t h a
--l <- toOptions $ mapraw_options t
  pure $ TransformEx r
  where
    doImports [] = return []
    doImports ((TransformEx ts):r) = case cast ts of
      Nothing -> Left "Bad import"
      Just ts' -> do { r'  <- doImports r ; return $ ts' : r' }

evalTransformRaw'
  :: forall var ty sym en fk att gen sk x y gen' sk' x' y'
  .  (ShowOrdTypeableN '[var, ty, sym, en, fk, att, gen, sk, x, y, gen', sk', x', y'])
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
    addImportGens x = foldr Map.union x $ map tGens is
    addImportSks  y = foldr Map.union y $ map tSks is

    gens'' = I.gens $ pres src'
    sks''  = I.sks  $ pres src'
    gens'  = I.gens $ pres dst'
    sks'   = I.sks  $ pres dst'
    gens0  =  filter (\(x,_) -> x `member'` gens'') sec
    sks0   =  filter (\(x,_) -> x `member'` sks'' ) sec

    evalGens []             = pure $ Map.empty
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
    evalTerm (RawApp x [])     | x `member'` gens''                     = do
      pure $ Gen $ fromJust $ cast x
    evalTerm (RawApp x [])     | x `member'` sks'                       = do
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
        Nothing -> undefined
    evalTerm  (RawApp v l)                                              = do
      l' <- mapM evalTerm l
      case cast v :: Maybe sym of
        Just x  -> pure $ Sym x l'
        Nothing -> undefined

    evalPath :: RawTerm -> Err (Term Void Void Void en fk Void gen' Void)
    evalPath (RawApp x [])     | x `member'` gens'                      = do
      pure $ Gen $ fromJust $ cast x
    evalPath (RawApp x (a:[])) | x `member'` (sch_fks $ I.schema dst')  = do
      a' <- evalPath a
      case cast x of
        Just x'2 -> return $ Fk x'2 a'
        Nothing  -> undefined
    evalPath _                                                          = undefined
