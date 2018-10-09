{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Transform where
import Prelude hiding (EQ)
import Data.Set as Set
import Data.Map.Strict as Map
import Language.Common
import Language.Term
import Language.Instance as I
import Language.Mapping
import Language.Query
import Data.Void
import Language.Schema as S
import Data.Typeable
import Data.Maybe
import Data.List


transToMor :: (Ord att', Ord fk', Ord en', Ord var, Ord ty,
                     Ord sym, Ord gen, Ord sk, Ord gen', Ord sk', Show var, Show ty,
                     Show sym, Show en', Show fk', Show att', Show gen, Show sk,
                     Show gen', Show sk') =>
                    Transform var ty sym en' fk' att' gen sk x1 y1 gen' sk' x2 y2
                    -> Morphism var ty sym en' fk' att' gen sk en' fk' att' gen' sk'
transToMor (Transform src' dst' gens' sks') = Morphism (instToCol (I.schema src') $ pres src') (instToCol (I.schema src') $ pres dst') ens0 fks0 atts0 gens' sks'
 where ens0 = Prelude.foldr (\en' m -> Map.insert en' en' m) Map.empty $ Set.toList $ S.ens $ I.schema src'
       fks0 = Prelude.foldr (\(fk,(_,_)) m -> Map.insert fk (Fk fk $ Var ()) m) Map.empty $ Map.toList $ S.fks $ I.schema src'
       atts0= Prelude.foldr (\(fk,_) m -> Map.insert fk (Att fk $ Var ()) m) Map.empty $ Map.toList $ S.atts $ I.schema src'

data Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  = Transform
  { srcT :: Instance var ty sym en fk att gen sk x y
  , dstT :: Instance var ty sym en fk att gen' sk' x' y'
  , gens :: Map gen (Term Void Void Void en fk Void gen' Void)
  , sks  :: Map sk  (Term Void  ty   sym  en fk att  gen' sk')
  }

data TransformEx :: * where
  TransformEx :: forall var ty sym en fk att gen sk x y gen' sk' x' y' .
   (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Show gen', Show sk', Show x', Show y') =>
    Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> TransformEx

deriving instance Show TransformEx


instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk,
          Show x, Show y, Show gen', Show sk', Show x', Show y')
  => Show (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  show (Transform _ _ gens' sks') = "transform {" ++
    "generators\n\t"  ++ intercalate "\n\t" ens'' ++
    "\nnulls\n\t" ++ intercalate "\n\t" fks'' ++ " }"
   where ens'' = Prelude.map (\(s,t) -> show s ++ " -> " ++ show t) $ Map.toList gens'
         fks'' = Prelude.map (\(k,s) -> show k ++ " -> " ++ show s) $ Map.toList sks'


instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Eq x, Eq y, Eq gen', Eq sk', Eq x', Eq y')
  => Eq (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
  (==) (Transform s1 s2 gens' sks') (Transform s1' s2' gens'' sks'')
    = (s1 == s1') && (s2 == s2') && (gens' == gens'') && (sks' == sks'')


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
 deriving Show

data TransExpRaw' = TransExpRaw' {
    transraw_src :: InstanceExp
  , transraw_dst :: InstanceExp
  , transraw_gens  :: [(String, RawTerm)]
  , transraw_options :: [(String, String)]
} deriving (Show)

typecheckTransform ::  (Show att, Ord var, Show var, Typeable en,  Ord en, Show en,  Typeable sym, Typeable att, Typeable fk, Show fk,
     Ord att, Ord en, Ord fk, Ord ty, Show ty, Show sym, Ord sym, Ord gen, Ord sk, Ord x, Ord y, Ord gen', Ord sk', Ord x', Ord y',
     Show gen, Show sk, Show x, Show y, Show gen', Show sk', Show x', Show y') =>
 Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> Err (Transform var ty sym en fk att gen sk x y gen' sk' x' y')
typecheckTransform m = do _ <- typeOfMor $ transToMor m
                          _ <- validateTransform m
                          return m


validateTransform :: forall var ty sym en fk att gen sk x y gen' sk' x' y' .
   (Show att, Ord var, Show var, Typeable en,  Ord en, Show en,  Typeable sym, Typeable att, Typeable fk, Show fk,
     Ord att, Ord en, Ord fk, Ord ty, Show ty, Show sym, Ord sym, Ord gen, Ord sk, Ord x, Ord y, Ord gen', Ord sk', Ord x', Ord y',
     Show gen, Show sk, Show x, Show y, Show gen', Show sk', Show x', Show y') =>
 Transform var ty sym en fk att gen sk x y gen' sk' x' y'  -> Err (Transform var ty sym en fk att gen sk x y gen' sk' x' y')
validateTransform (m@(Transform src' dst' _ _)) = do _ <- mapM f (Set.toList $ eqs $ pres src')
                                                     pure m
 where f :: (EQ Void ty sym en fk att gen sk) -> Err ()
       f (EQ (l,r)) = let l' = trans (transToMor m) l
                          r' = trans (transToMor m) r :: Term Void ty sym en fk att gen' sk'
                      in if dp dst' (EQ ( l',   r'))
                             then pure ()
                             else Left $ show l ++ " = " ++ show r ++ " translates to " ++ show l' ++ " = " ++ show r' ++ " which is not provable"


evalTransformRaw :: forall var ty sym en fk att gen sk x y gen' sk' x' y' .
  (Ord var, Ord ty, Ord sym, Show att, Show sym, Show var, Show ty, Typeable en, Ord en, Show en, Typeable sym, Typeable att, Typeable fk, Show fk,
    Ord att,  Ord en, Ord fk, Typeable sk', Typeable gen', Ord sk', Ord gen', Ord sk, Ord gen, Typeable sk, Typeable gen, Ord x, Ord y, Ord x', Ord y'
    , Show gen, Show gen', Show sk ,Show x, Show y, Show x', Show y', Show sk') =>
  Instance var ty sym en fk att gen sk x y -> Instance var ty sym en fk att gen' sk' x' y' -> TransExpRaw'
 -> Err (TransformEx)
evalTransformRaw src' dst' (TransExpRaw' _ _ sec _) =
  do x <- f' gens0
     y <- f  sks0
     _ <- check
     z <- typecheckTransform $ Transform src' dst' x y
     pure $ TransformEx z
 where
  non0 = Prelude.filter (\(x,_) -> not ( (elem' x $ keys' gens') || (elem' x $ keys' sks') )) sec
  check = if Prelude.null non0 then pure () else Left $ "Not a gen or null: " ++ show non0
  gens0 =  Prelude.filter (\(x,_) -> elem' x $ keys' gens') sec
  sks0 =  Prelude.filter (\(x,_) -> elem' x $ keys' sks') sec

  keys' = fst . unzip
  gens' = Map.toList $ I.gens $ pres dst'
  sks' = Map.toList $ I.sks $ pres dst'
  f' [] = pure $ Map.empty
  f'  ((gen, t):ts) = do t'   <- h t
                         rest <- f' ts
                         gen' <- cast' gen $ "Not a generator: " ++ gen
                         pure $ Map.insert gen' t' rest

  f [] = pure $ Map.empty
  f  ((gen, t):ts) = do t'   <- g t
                        rest <- f ts
                        gen' <- cast' gen $ "Not a null: " ++ gen
                        pure $ Map.insert gen' t' rest

  g ::  RawTerm -> Err (Term Void ty sym en fk att gen' sk')
  g  (RawApp x []) | elem' x (keys' gens') = pure $ Gen $ fromJust $ cast x
  g  (RawApp x []) | elem' x (keys' sks') = pure $ Sk $ fromJust $ cast x

  g  (RawApp x (a:[])) | elem' x (keys' $ Map.toList $ sch_fks $ I.schema dst') = do a' <- g a
                                                                                     case cast x of
                                                                                      Just x' -> return $ Fk x' a'
                                                                                      Nothing -> undefined
  g  (RawApp x (a:[])) | elem' x (keys' $ Map.toList $ sch_atts $ I.schema dst') = do a' <- g a
                                                                                      case cast x of
                                                                                        Just x' -> return $ Att x' a'
                                                                                        Nothing -> undefined
  g  (RawApp v l) = do l' <- mapM g l
                       case cast v :: Maybe sym of
                                  Just x -> pure $ Sym x l'
                                  Nothing -> undefined

  h :: RawTerm -> Err (Term Void Void Void en fk Void gen' Void)
  h  (RawApp x []) | elem' x (keys' gens') = pure $ Gen $ fromJust $ cast x

  h  (RawApp x (a:[])) | elem' x (keys' $ Map.toList $ sch_fks $ I.schema dst') = do a' <- h a
                                                                                     case cast x of
                                                                                      Just x' -> return $ Fk x' a'
                                                                                      Nothing -> undefined
  h _ = undefined


