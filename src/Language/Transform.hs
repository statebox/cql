{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs
           , KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances
           , MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators, LiberalTypeSynonyms, ImpredicativeTypes
           , UndecidableInstances, FunctionalDependencies
#-}

module Language.Transform where

import Prelude hiding (EQ)
import qualified Data.Map.Strict as Map
import Data.Map (Map, mapWithKey)
import Data.Maybe
import qualified Data.Set as Set
import Data.Typeable
import Data.Void
import Language.Common
import Language.Term
import Language.Instance as I
import Language.Mapping as M
import Language.Query
import Language.Schema as S
import Language.Options


evalSigmaTrans
  :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord gen', Ord sk, Ord sk', Ord x', Ord y', Eq x, Eq y, Eq en',
      Ord fk', Ord att', Show var, Show att', Show fk', Show sym, Ord en',
      Show en, Show en', Show ty, Show sym, Show var, Show fk, Show fk', Show att, Show att',
      Show gen, Show sk, Show gen', Show sk', Show x', Show y' )
  => Mapping var ty sym en fk att en' fk' att'
  -> Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  -> Options
  -> Err (Transform var ty sym en' fk' att' gen sk (Carrier en' fk' gen) (TalgGen en' fk' att' gen sk) gen' sk' (Carrier en' fk' gen') (TalgGen en' fk' att' gen' sk'))
evalSigmaTrans f (Transform src0 dst0 gens' sks') o =
 do src' <- evalSigmaInst f src0 o
    dst' <- evalSigmaInst f dst0 o
    pure $ Transform src' dst' gens'' sks''
 where gens'' = changeEn' (M.fks f) (M.atts f) <$> gens'
       sks''  = changeEn  (M.fks f) (M.atts f) <$> sks'

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

evalDeltaSigmaUnit
  :: forall var ty sym en fk att gen sk x y en' fk' att'
   . ( Eq x, Eq y, Eq en'
     , Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Ord fk', Ord att', Ord en', Ord x, Ord y
     , Show var, Show att', Show fk', Show sym, Show en, Show en', Show ty, Show sym, Show var, Show fk, Show fk', Show att, Show att', Show gen, Show sk, Show x, Show y
     )
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
   f j gen en' = Gen (en', nf   (algebra j) (Gen gen))
   g j sk  _   = up20 $    nf'' (algebra j) (Sk sk)

evalDeltaSigmaCoUnit :: forall var ty sym en fk att gen sk x y en' fk' att'.
     (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y, Eq en',
      Ord fk', Ord att', Show var, Show att', Show fk', Show sym, Ord en',
      Show en, Show en', Show ty, Show sym, Show var, Show fk, Show fk', Show att, Show att',
      Show gen, Show sk, Show x, Show y, Ord x, Ord y)
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en' fk' att' gen sk x y
  -> Options
  -> Err (Transform var ty sym en' fk' att' (en, x) y (Carrier en' fk' (en, x)) (TalgGen en' fk' att' (en, x) y) gen sk x y)
evalDeltaSigmaCoUnit m i o = do j <- evalDeltaInst m i o
                                k <- evalSigmaInst m j o
                                return $ Transform k i (Map.fromList $ fmap (f j) $ Map.toList $ I.gens $ pres k) $ (Map.fromList $ fmap (g j) $ Map.toList $ I.sks $ pres k)
 where
       f _ ((en', x), _) = ((en',x), repr  (algebra i) x)
       g _ (sk      , _) = (sk     , repr' (algebra i) sk)


evalDeltaTrans
 :: ( Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord gen', Ord sk, Ord sk', Ord x', Ord y', Eq x, Eq y, Eq en',
      Ord fk', Ord att', Show var, Show att', Show fk', Show sym, Ord en',
      Show en, Show en', Show ty, Show sym, Show var, Show fk, Show fk', Show att, Show att',
      Show gen, Show sk, Show gen', Show sk', Show x', Show y', Show x, Show y, Ord x, Ord y)
  => Mapping var ty sym en fk att en' fk' att'
  -> Transform var ty sym en' fk' att' gen sk x y gen' sk' x' y'
  -> Options
  -> Err (Transform var ty sym en fk att (en,x) y (en,x) y (en,x') y' (en,x') y')
evalDeltaTrans m h o = do
  i <- evalDeltaInst m (srcT h) o
  j <- evalDeltaInst m (dstT h) o
  pure $ Transform i j (gens' i) (sks' i)
 where
   gens' i = mapWithKey (\(_,x) en' -> Gen (en', nf   (algebra $ dstT h) $ transTrans'  h $ repr  (algebra $ srcT h) x)) $ I.gens $ pres i
   sks'  i = mapWithKey (\y     _   -> up20 $    nf'' (algebra $ dstT h) $ transTrans'' h $ repr' (algebra $ srcT h) y)  $ I.sks  $ pres i

-- TODO order constraints
transToMor
  :: ( Ord  var, Ord  fk', Ord  sym, Ord  en', Ord  ty, Ord  att',  Ord  gen, Ord  sk, Ord  gen', Ord sk'
     , Show var, Show fk', Show sym, Show en', Show ty, Show att', Show gen, Show sk, Show gen', Show sk')
  => Transform var ty sym en' fk' att' gen sk x1  y1       gen' sk' x2 y2
  -> Morphism  var ty sym en' fk' att' gen sk en' fk' att' gen' sk'
transToMor (Transform src' dst' gens' sks') =
  Morphism (instToCol (I.schema src') (pres src'))
           (instToCol (I.schema src') (pres dst'))
           ens0 fks0 atts0 gens' sks'
  where
    ens0  = Map.fromSet (\en0   -> en0            ) (S.ens  $ I.schema src')
    fks0  = mapWithKey  (\fk  _ -> Fk  fk (Var ())) (S.fks  $ I.schema src')
    atts0 = mapWithKey  (\fk  _ -> Att fk (Var ())) (S.atts $ I.schema src')

-- | Map from one 'Instance' to another of the same 'Schema'.
data Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  = Transform
  { srcT :: Instance var ty sym en fk att gen sk x y
  , dstT :: Instance var ty sym en fk att gen' sk' x' y'
  , gens :: Map gen (Term Void Void Void en fk Void gen' Void)
  , sks  :: Map sk  (Term Void ty   sym  en fk att  gen' sk')
  }

tGens :: Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> Map gen (Term Void Void Void en fk Void gen' Void)
tGens = gens

tSks :: Transform var ty sym en fk att gen sk x y gen' sk' x' y' -> Map sk  (Term Void ty   sym  en fk att  gen' sk')
tSks = sks

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

getOptionsTransform :: TransformExp -> [(String, String)]
getOptionsTransform (TransformVar _) = [] 
getOptionsTransform (TransformId _) = []                                                 
getOptionsTransform (TransformSigmaDeltaUnit _ _ o) = o
getOptionsTransform (TransformSigmaDeltaCoUnit _ _ o) = o
getOptionsTransform (TransformDelta _ _ o) = o          
getOptionsTransform (TransformSigma _ _ o) = o          
getOptionsTransform (TransformRaw (TransExpRaw' _ _ _ o _)) = o
getOptionsTransform _ = error "other transforms" 

instance Deps TransformExp where
  deps (TransformVar v) = [(v,TRANSFORM)]  
  deps (TransformId i) = deps i                                                   
  deps (TransformSigmaDeltaUnit f i _) = (deps f) ++ (deps i)
  deps (TransformSigmaDeltaCoUnit f i _) = (deps f) ++ (deps i)
  deps (TransformDelta f i _) = (deps f) ++ (deps i)           
  deps (TransformSigma f i _) = (deps f) ++ (deps i)          
  deps (TransformRaw (TransExpRaw' s t _ _ i)) = (deps s) ++ (deps t) ++ (concatMap deps i)
  deps _ = error "other transforms" 

data TransformExp  where
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

data TransExpRaw'
  = TransExpRaw'
  { transraw_src     :: InstanceExp
  , transraw_dst     :: InstanceExp
  , transraw_gens    :: [(String, RawTerm)]
  , transraw_options :: [(String, String)]
  , transraw_imports :: [TransformExp]
} deriving Show

typecheckTransform ::  (Show att, Ord var, Show var, Typeable en,  Ord en, Show en,  Typeable sym, Typeable att, Typeable fk, Show fk,
     Ord att, Ord en, Ord fk, Ord ty, Show ty, Show sym, Ord sym, Ord gen, Ord sk, Ord x, Ord y, Ord gen', Ord sk', Ord x', Ord y',
     Show gen, Show sk, Show x, Show y, Show gen', Show sk', Show x', Show y')
  =>      Transform var ty sym en fk att gen sk x y gen' sk' x' y'
  -> Err ()
typecheckTransform m = typeOfMor $ transToMor m
  

validateTransform :: forall var ty sym en fk att gen sk x y gen' sk' x' y' .
   (Show att, Ord var, Show var, Typeable en,  Ord en, Show en,  Typeable sym, Typeable att, Typeable fk, Show fk,
     Ord att, Ord en, Ord fk, Ord ty, Show ty, Show sym, Ord sym, Ord gen, Ord sk, Ord x, Ord y, Ord gen', Ord sk', Ord x', Ord y',
     Show gen, Show sk, Show x, Show y, Show gen', Show sk', Show x', Show y') =>
 Transform var ty sym en fk att gen sk x y gen' sk' x' y'  -> Err ()
validateTransform (m@(Transform src' dst' _ _)) = do
  _ <- mapM_ f (Set.toList $ eqs $ pres src')
  pure ()
 where f :: (EQ Void ty sym en fk att gen sk) -> Err ()
       f (EQ (l,r)) = let l' = trans (transToMor m) l
                          r' = trans (transToMor m) r :: Term Void ty sym en fk att gen' sk'
                      in if dp dst' (EQ ( l',   r'))
                             then pure ()
                             else Left $ show l ++ " = " ++ show r ++ " translates to " ++ show l' ++ " = " ++ show r' ++ " which is not provable"


evalTransformRaw
  :: forall var ty sym en fk att gen sk x y gen' sk' x' y'
   . ( Ord var, Ord ty, Ord sym, Ord en
     , Ord att, Ord en, Ord fk, Ord sk', Ord gen', Ord sk, Ord gen, Ord x, Ord y, Ord x', Ord y'
     , Show en, Show fk
     , Show att, Show sym, Show var, Show ty, Show gen, Show gen', Show sk, Show x, Show y, Show x', Show y', Show sk'
     , Typeable sym, Typeable att, Typeable fk, Typeable en, Typeable sk, Typeable gen
     , Typeable var, Typeable ty, Typeable x, Typeable y, Typeable x', Typeable y',  Typeable sk', Typeable gen')
  => Instance var ty sym en fk att gen  sk  x  y
  -> Instance var ty sym en fk att gen' sk' x' y'
  -> TransExpRaw'
  -> [TransformEx]
  -> Err (TransformEx)
evalTransformRaw s t h is = 
  do (a :: [Transform var ty sym en fk att gen sk x y gen' sk' x' y']) <- g is
     r <- evalTransformRaw' s t h a
      --l <- toOptions $ mapraw_options t
     pure $ TransformEx r
 where
   --g :: forall var ty sym en fk att gen sk x y gen' sk' x' y'. (Typeable sym, Typeable att, Typeable fk, Typeable en, Typeable sk, Typeable gen
   --  , Typeable var, Typeable ty, Typeable x, Typeable y, Typeable x', Typeable y', Typeable sk', Typeable gen') 
    -- => [TransformEx] -> Err [Transform var ty sym en fk att gen sk x y gen' sk' x' y']
   g [] = return []
   g ((TransformEx ts):r) = case cast ts of
                            Nothing -> Left "Bad import"
                            Just ts' -> do r'  <- g r
                                           return $ ts' : r'

evalTransformRaw'
  :: forall var ty sym en fk att gen sk x y gen' sk' x' y'
   . ( Ord var, Ord ty, Ord sym, Ord en
     , Ord att, Ord en, Ord fk, Typeable sk', Typeable gen', Ord sk', Ord gen', Ord sk, Ord gen, Ord x, Ord y, Ord x', Ord y'
     , Show en, Show fk
     , Show att, Show sym, Show var, Show ty, Show gen, Show gen', Show sk, Show x, Show y, Show x', Show y', Show sk'
     , Typeable sym, Typeable att, Typeable fk, Typeable en, Typeable sk, Typeable gen
     , Typeable var, Typeable ty, Typeable x, Typeable y, Typeable x', Typeable y')
  => Instance var ty sym en fk att gen  sk  x  y
  -> Instance var ty sym en fk att gen' sk' x' y'
  -> TransExpRaw'
  -> [Transform var ty sym en fk att gen sk x y gen' sk' x' y']
  -> Err (Transform var ty sym en fk att gen sk x y gen' sk' x' y')
evalTransformRaw' src' dst' (TransExpRaw' _ _ sec _ _) is =
  do x <- f' gens0
     y <- f  sks0
     return $ Transform src' dst' (x' x) (y' y)
 where
  x' x = foldr Map.union x $ map tGens is
  y' y = foldr Map.union y $ map tSks is
  gens'' = I.gens $ pres src'
  sks''  = I.sks  $ pres src'

  --check = if Prelude.null non0 then pure () else Left $ "Not a gen or null: " ++ show non0
  gens0  =  filter (\(x,_) -> x `member'` gens'') sec
  sks0   =  filter (\(x,_) -> x `member'` sks'' ) sec

  gens'  = I.gens $ pres dst'
  sks'   = I.sks  $ pres dst'

  f' []             = pure $ Map.empty
  f'  ((gen, t):ts) = do t'   <- h t
                         rest <- f' ts
                         gen' <- note ("Not a generator: " ++ gen) (cast gen)
                         pure $ Map.insert gen' t' rest

  f []             = pure $ Map.empty
  f  ((gen, t):ts) = do t'   <- g t
                        rest <- f ts
                        gen' <- note ("Not a null: " ++ gen) (cast gen)
                        pure $ Map.insert gen' t' rest

  g ::  RawTerm -> Err (Term Void ty sym en fk att gen' sk')
  g  (RawApp x [])     | x `member'` gens''                     = pure $ Gen $ fromJust $ cast x

  g  (RawApp x [])     | x `member'` sks'                       = pure $ Sk  $ fromJust $ cast x

  g  (RawApp x (a:[])) | x `member'` (sch_fks $ I.schema dst')  = do a' <- g a
                                                                     case cast x of
                                                                       Just x'2 -> return $ Fk x'2 a'
                                                                       Nothing -> undefined
  g  (RawApp x (a:[])) | x `member'` (sch_atts $ I.schema dst') = do a' <- g a
                                                                     case cast x of
                                                                       Just x'2 -> return $ Att x'2 a'
                                                                       Nothing -> undefined
  g  (RawApp v l)                                               = do l' <- mapM g l
                                                                     case cast v :: Maybe sym of
                                                                       Just x -> pure $ Sym x l'
                                                                       Nothing -> undefined

  h :: RawTerm -> Err (Term Void Void Void en fk Void gen' Void)
  h (RawApp x [])     | x `member'` gens'                      = pure $ Gen $ fromJust $ cast x
  h (RawApp x (a:[])) | x `member'` (sch_fks $ I.schema dst')  = do a' <- h a
                                                                    case cast x of
                                                                      Just x'2 -> return $ Fk x'2 a'
                                                                      Nothing -> undefined
  h _                                                          = undefined
