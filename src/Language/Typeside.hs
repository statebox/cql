{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Typeside where
import Prelude hiding (EQ)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map.Strict as Map
import Data.Map.Strict hiding (foldr)
import Language.Common
import Language.Term
import Data.Void
import Language.Prover
import Language.Options
import Data.Typeable
import Data.List (nub)


type Ty = String
type Sym = String
type Var = String

fromList'' :: (ShowOrd k) => [k] -> Err (Set k)
fromList'' (k:l) = do l' <- fromList'' l
                      if Set.member k l'
                      then Left $ "Duplicate binding: " ++ (show k)
                      else pure $ Set.insert k l'
fromList'' [] = return Set.empty

fromList' :: (ShowOrd k) => [(k,v)] -> Err (Map k v)
fromList' ((k,v):l) = do l' <- fromList' l
                         if Map.member k l'
                         then Left $ "Duplicate binding: " ++ (show k)
                         else pure $ Map.insert k v l'
fromList' [] = return Map.empty

-- | A user-defined kind for customisation of data types.
data Typeside var ty sym
  = Typeside
  { tys  :: Set ty
  , syms :: Map sym ([ty], ty)
  , eqs  :: Set (Ctx var ty, EQ var ty sym Void Void Void Void Void)
  , eq   :: Ctx var ty -> EQ var ty sym Void Void Void Void Void -> Bool
  }

initialTypeside :: Typeside Void Void Void
initialTypeside = Typeside Set.empty Map.empty Set.empty (\_ _ -> undefined) --todo: use absurd

data TypesideEx :: * where
  TypesideEx
    :: forall var ty sym. (ShowOrdTypeable3 var ty sym) =>
    Typeside var ty sym
    -> TypesideEx

deriving instance Show (TypesideEx)


instance (Eq var, Eq ty, Eq sym) => Eq (Typeside var ty sym) where
  (==) (Typeside tys'  syms'  eqs'  _)
       (Typeside tys'' syms'' eqs'' _)
    = (tys' == tys'') && (syms' == syms'') && (eqs' == eqs'')

instance (Show var, Show ty, Show sym) => Show (Typeside var ty sym) where
  show (Typeside tys' syms' eqs' _) = "typeside {\n" ++
    "types\n\t"    ++ intercalate "\n\t" (Prelude.map show $ Set.toList tys') ++
    "\nfunctions\n\t" ++ intercalate "\n\t" syms'' ++
    "\nequations\n\t"  ++ intercalate "\n\t" eqs'' ++ " }"
   where syms'' = Prelude.map (\(k,(s,t)) -> show k ++ " : " ++ show s ++ " -> " ++ show t) $ Map.toList syms'
         eqs''  = Prelude.map (\(k,s) -> "forall " ++ showCtx k ++ " . " ++ show s) $ Set.toList eqs'

showCtx :: (Show a1, Show a2) => Map a1 a2 -> [Char]
showCtx m = intercalate " " $ Prelude.map (\(k,v) -> show k ++ " : " ++ show v) $ Map.toList m

typecheckTypeside
  :: (ShowOrd3 var ty sym)
  => Typeside var ty sym
  -> Err ()
typecheckTypeside = typeOfCol . tsToCol

data TypesideRaw' = TypesideRaw' {
    tsraw_tys  :: [String]
  , tsraw_syms :: [(String, ([String], String))]
  , tsraw_eqs  :: [([(String, Maybe String)], RawTerm, RawTerm)]
  , tsraw_options :: [(String, String)]
  , tsraw_imports :: [TypesideExp]
} deriving (Eq, Show)


tsToCol :: (ShowOrd3 var ty sym) => Typeside var ty sym -> Collage var ty sym Void Void Void Void Void
tsToCol (Typeside t s e _) = Collage e' t Set.empty s Map.empty Map.empty Map.empty Map.empty
 where e' = Set.map (\(g,x)->(Map.map Left g, x)) e

evalTypesideRaw :: TypesideRaw' -> [TypesideEx] -> Err TypesideEx
evalTypesideRaw t a' =
 do a <- g a'
    r <- evalTypesideRaw' t a
    l <- toOptions $ tsraw_options t
    p <- createProver (tsToCol r) l
    pure $ TypesideEx $ Typeside (tys r) (syms r) (eqs r) (f p)
 where
   f p ctx = prove p (Map.map Left ctx)
   g :: forall var ty sym. (Typeable var, Typeable ty, Typeable sym) => [TypesideEx] -> Err [Typeside var ty sym]
   g [] = return []
   g ((TypesideEx ts):r) = case cast ts of
                            Nothing -> Left "Bad import"
                            Just ts' -> do r'  <- g r
                                           return $ ts' : r'

evalTypesideRaw' :: TypesideRaw'  -> [Typeside Var Ty Sym] -> Err (Typeside Var Ty Sym)
evalTypesideRaw' (TypesideRaw' ttys tsyms teqs _ _) is =
  do tys' <- fromList'' ttys
     syms' <- fromList' tsyms
     eqs' <- f (b syms') teqs
     return $ Typeside (Set.union a tys') (b syms') (Set.union c eqs') undefined -- leave prover blank
 where a = foldr Set.union Set.empty $ fmap tys is
       b syms' = foldr (\(f',(s,t)) m -> Map.insert f' (s,t) m) syms' $ concatMap (Map.toList . syms) is
       c = foldr Set.union Set.empty $ fmap eqs is
       f _ [] = pure $ Set.empty
       f syms' ((ctx, lhs, rhs):eqs') = do ctx' <- check syms' ctx lhs rhs
                                           lhs' <- g syms' ctx' lhs
                                           rhs' <- g syms' ctx' rhs
                                           rest <- f syms' eqs'
                                           pure $ Set.insert (ctx', EQ (lhs', rhs')) rest
       g _ ctx (RawApp v []) | Map.member v ctx = pure $ Var v
       g syms' ctx (RawApp v l) = do l' <- mapM (g syms' ctx) l
                                     pure $ Sym v l'
       check _ [] _ _ = pure Map.empty
       check syms' ((v,t):l) lhs rhs = do {x <- check syms' l lhs rhs; t' <- infer v t syms' lhs rhs; pure $ Map.insert v t' x}
       infer _ (Just t) _ _ _= return t
       infer v _ syms' lhs rhs = let t1s = nub $ typesOf v syms' lhs
                                     t2s = nub $ typesOf v syms' rhs
                                 in case (t1s, t2s) of
                                       (t1 : [], t2 : []) -> if t1 == t2 then return t1 else Left $ "Type mismatch on " ++ show v ++ " in " ++ show lhs ++ " = " ++ show rhs ++ ", types are " ++ show t1 ++ " and " ++ show t2
                                       (t1 : t2 : _, _) -> Left $ "Conflicting types for " ++ show v ++ " in " ++ show lhs ++ ": " ++ show t1 ++ " and " ++ show t2
                                       (_, t1 : t2 : _) -> Left $ "Conflicting types for " ++ show v ++ " in " ++ show rhs ++ ": " ++ show t1 ++ " and " ++ show t2
                                       ([], t : []) -> return t
                                       (t : [], []) -> return t
                                       ([], []) -> Left $ "Ambiguous variable: " ++ show v
       typesOf _ _ (RawApp _ []) = []
       typesOf v syms' (RawApp f' as) =
        let fn (a',t) = case a' of
                          RawApp v' [] -> if v == v' then [t] else []
                          RawApp _ _ -> typesOf v syms' a'
        in concatMap fn $ zip as $ maybe [] fst $ Map.lookup f' syms'



-- there are practical haskell type system related reasons to not want this to be a gadt
data TypesideExp where
  TypesideVar :: String -> TypesideExp
  TypesideInitial :: TypesideExp
  TypesideRaw :: TypesideRaw' -> TypesideExp

instance Deps TypesideExp where
  deps (TypesideVar v) = [(v, TYPESIDE)]
  deps TypesideInitial = []
  deps (TypesideRaw (TypesideRaw' _ _ _ _ i)) = concatMap deps i


deriving instance Eq TypesideExp
deriving instance Show TypesideExp

--todo: make pretty
