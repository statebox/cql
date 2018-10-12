{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Transform where
import Prelude hiding (EQ)
import Data.Set as Set
import Data.Map.Strict as Map
import Language.Common
import Language.Term
import Language.Instance as I
import Language.Mapping as M
import Language.Query
import Data.Void
import Language.Schema as S
import Data.Typeable
import Data.Maybe
import Data.List
import Language.Options

evalSigmaTrans
  :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord gen', Ord sk, Ord sk', Ord x', Ord y', Eq x, Eq y, Eq en',
      Ord fk', Ord att', Show var, Show att', Show fk', Show sym, Ord en',
      Show en, Show en', Show ty, Show sym, Show var, Show fk, Show fk', Show att, Show att',
      Show gen, Show sk, Show gen', Show sk', Show x', Show y' )
  => Mapping var ty sym en fk att en' fk' att'
  -> Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> Options
  -> Err (Transform var ty sym en' fk' att' gen sk (GTerm en' fk' gen) (TTerm en' fk' att' gen sk) gen' sk' (GTerm en' fk' gen') (TTerm en' fk' att' gen' sk'))
evalSigmaTrans f (Transform src0 dst0 gens' sks') o =
 do src' <- evalSigmaInst f src0 o
    dst' <- evalSigmaInst f dst0 o
    return $ Transform src' dst' gens'' sks''
 where gens'' = Map.fromList $ Prelude.map (\(gen,term) -> (gen, changeEn' (M.fks f) (M.atts f) term)) $ Map.toList gens'
       sks'' = Map.fromList $ Prelude.map (\(sk,term) -> (sk, changeEn (M.fks f) (M.atts f) term)) $ Map.toList sks'

gensAlt :: Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> Map gen (Term Void Void Void en fk Void gen' Void)
gensAlt (Transform _ _ gens' _) = gens'

sksAlt :: Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> Map sk (Term Void  ty   sym  en fk att  gen' sk')
sksAlt (Transform _ _ _ sks') = sks'

transTrans :: (Ord gen, Ord sk) =>
 Transform Void ty sym en' fk' att' gen sk x y gen' sk' x' y' ->
 Term Void ty sym en' fk' att' gen sk -> Term Void ty sym en' fk' att' gen' sk'
transTrans _ (Var v) = Var v
transTrans t (Sym f as) = Sym f $ fmap (transTrans t) as
transTrans t (Fk f a) = Fk f $ transTrans t a
transTrans t (Att f a) = Att f $ transTrans t a
transTrans t (Gen g) = up12 $ fromJust $ Map.lookup g $ gensAlt t
transTrans t (Sk g) = fromJust $ Map.lookup g $ sksAlt t


transTrans'' :: (Ord gen, Ord sk) =>
 Transform var ty sym en' fk' att' gen sk x y gen' sk' x' y' ->
 Term Void ty sym en' fk' att' gen sk -> Term Void ty sym en' fk' att' gen' sk'
transTrans'' _ (Var v) = Var v
transTrans'' t (Sym f as) = Sym f $ fmap (transTrans'' t) as
transTrans'' t (Fk f a) = Fk f $ transTrans'' t a
transTrans'' t (Att f a) = Att f $ transTrans'' t a
transTrans'' t (Gen g) = up12 $ fromJust $ Map.lookup g $ gensAlt t
transTrans'' t (Sk g) = fromJust $ Map.lookup g $ sksAlt t

transTrans' :: (Ord gen) => Transform var ty sym en' fk' att' gen sk x y gen' sk' x' y' ->
 Term Void Void Void en' fk' Void gen Void -> Term Void Void Void en' fk' Void gen' Void
transTrans' _ (Var v) = absurd v
transTrans' _ (Sym f _) = absurd f
transTrans' t (Fk f a) = Fk f $ transTrans' t a
transTrans' _ (Att f _) = absurd f
transTrans' t (Gen g) = fromJust $ Map.lookup g $ gensAlt t
transTrans' _ (Sk g) = absurd g

up20 :: Term Void ty sym Void Void Void Void y' -> Term Void ty sym en fk att gen y'
up20 (Var v) = Var v
up20 (Sym f as) = Sym f $ fmap up20 as
up20 (Fk f _) = absurd f
up20 (Att f _) = absurd f
up20 (Gen g) = absurd g
up20 (Sk k) = Sk k

evalDeltaSigmaUnit :: forall var ty sym en fk att gen sk x y en' fk' att'.
     (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y, Eq en',
      Ord fk', Ord att', Show var, Show att', Show fk', Show sym, Ord en',
      Show en, Show en', Show ty, Show sym, Show var, Show fk, Show fk', Show att, Show att',
      Show gen, Show sk, Show x, Show y, Ord x, Ord y) 
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en fk att gen sk x y -> Options 
  -> Err (Transform var ty sym en fk att gen sk x y (en, GTerm en' fk' gen) (TTerm en' fk' att' gen sk) (en,GTerm en' fk' gen) (TTerm en' fk' att' gen sk)) 
evalDeltaSigmaUnit m i o = do j <- evalSigmaInst m i o
                              k <- evalDeltaInst m j o
                              return $ Transform i k (Map.fromList $ fmap (f j) $ Map.toList $ I.gens $ pres i) $ (Map.fromList $ fmap (g j) $ Map.toList $ I.sks $ pres i)
 where 
       f j (gen, en) = (gen, Gen (en, nf (algebra j) (Gen gen)))
       g j (sk,  ty) =  (sk, up20 $ nf'' (algebra j) (Sk sk))
       
evalDeltaSigmaCoUnit :: forall var ty sym en fk att gen sk x y en' fk' att'.
     (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y, Eq en',
      Ord fk', Ord att', Show var, Show att', Show fk', Show sym, Ord en',
      Show en, Show en', Show ty, Show sym, Show var, Show fk, Show fk', Show att, Show att',
      Show gen, Show sk, Show x, Show y, Ord x, Ord y) 
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en' fk' att' gen sk x y -> Options 
  -> Err (Transform var ty sym en' fk' att' (en, x) y (GTerm en' fk' (en, x)) (TTerm en' fk' att' (en, x) y) gen sk x y)
evalDeltaSigmaCoUnit m i o = do j <- evalDeltaInst m i o
                                k <- evalSigmaInst m j o
                                return $ Transform k i (Map.fromList $ fmap (f j) $ Map.toList $ I.gens $ pres k) $ (Map.fromList $ fmap (g j) $ Map.toList $ I.sks $ pres k)
 where 
       f j ((en', x), en) = ((en',x), repr (algebra i) x) 
       g j (sk,  ty) = (sk, repr' (algebra i) ( sk))       
{--
for (Pair<En1, X> gen : src().gens().keySet()) {
      gens.put(gen, I.algebra().repr(gen.second).map(Util.voidFn(), Util.voidFn(), Function.identity(), Util.voidFn(), Function.identity(), Util.voidFn()));
    }
    for (Y sk : src().sks().keySet()) {
      sks.put(sk, I.algebra().reprT(Term.Sk(sk)));
    }  --}

evalDeltaTrans
 :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord gen', Ord sk, Ord sk', Ord x', Ord y', Eq x, Eq y, Eq en',
      Ord fk', Ord att', Show var, Show att', Show fk', Show sym, Ord en',
      Show en, Show en', Show ty, Show sym, Show var, Show fk, Show fk', Show att, Show att',
      Show gen, Show sk, Show gen', Show sk', Show x', Show y', Show x, Show y, Ord x, Ord y) => Mapping var ty sym en fk att en' fk' att'
  -> Transform var ty sym en' fk' att' gen sk x y gen' sk' x' y' -> Options
  -> Err (Transform var ty sym en fk att (en,x) y (en,x) y (en,x') y' (en,x') y')
evalDeltaTrans m h o = do i <- evalDeltaInst m (srcT h) o
                          j <- evalDeltaInst m (dstT h) o
                          return $ Transform i j (gens' i) $ sks' i
 where
       gens' i = Map.fromList $ Prelude.map (\((gen,x),en') -> ((gen,x), Gen (en', nf (algebra $ dstT h) $ transTrans' h $ repr (algebra $ srcT h) x) )) $ Map.toList $ I.gens $ pres i
       sks' i = Map.fromList $ Prelude.map (\(y,_) -> (y, up20 $ nf'' (algebra $ dstT h) $ transTrans'' h $ repr' (algebra $ srcT h) y)) $ Map.toList $ I.sks $ pres i


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
   (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Ord x, Ord y, Ord gen', Ord sk', Ord x', Ord y',
    Typeable var, Typeable ty, Typeable sym, Typeable en, Typeable fk, Typeable att, Typeable gen, Typeable sk, Typeable x, Typeable y, Typeable gen', Typeable sk', Typeable x', Typeable y',
    Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Show gen', Show sk', Show x', Show y' ) =>
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
  TransformSigmaDeltaUnit :: MappingExp -> InstanceExp -> [(String,String)] -> TransformExp
  TransformSigmaDeltaCoUnit :: MappingExp -> InstanceExp -> [(String,String)] -> TransformExp
  TransformDeltaPiUnit :: MappingExp -> TransformExp
  TransformDeltaPiCoUnit :: MappingExp -> TransformExp
  TransformQueryUnit :: QueryExp -> TransformExp
  TransformQueryCoUnit :: MappingExp -> TransformExp
  TransformDelta :: MappingExp -> TransformExp -> [(String,String)] -> TransformExp
  TransformSigma :: MappingExp -> TransformExp -> [(String,String)] -> TransformExp
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
    , Show gen, Show gen', Show sk ,Show x, Show y, Show x', Show y', Show sk', Typeable var, Typeable ty, Typeable x, Typeable y, Typeable x', Typeable y') =>
  Instance var ty sym en fk att gen sk x y -> Instance var ty sym en fk att gen' sk' x' y' -> TransExpRaw'
 -> Err (TransformEx)
evalTransformRaw src' dst' (TransExpRaw' _ _ sec _) =
  do x <- f' gens0
     y <- f  sks0
     z <- typecheckTransform $ Transform src' dst' x y
     pure $ TransformEx z
 where

  gens'' = Map.toList $ I.gens $ pres src'
  sks'' = Map.toList $ I.sks $ pres src'
  --check = if Prelude.null non0 then pure () else Left $ "Not a gen or null: " ++ show non0
  gens0 =  Prelude.filter (\(x,_) -> elem' x $ keys' gens'') sec
  sks0 =  Prelude.filter (\(x,_) -> elem' x $ keys' sks'') sec

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


