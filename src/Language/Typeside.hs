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

module Language.Typeside where
import           Control.DeepSeq
import           Data.List        (nub)
import           Data.Map.Strict  hiding (foldr)
import qualified Data.Map.Strict  as Map
import           Data.Set         (Set)
import qualified Data.Set         as Set
import           Data.Typeable
import           Data.Void
import           Language.Common
import           Language.Options
import           Language.Prover
import           Language.Term
import           Prelude          hiding (EQ)

-- | A user-defined kind for customization of data types.
data Typeside var ty sym
  = Typeside
  { tys  :: Set ty
  , syms :: Map sym ([ty], ty)
  , eqs  :: Set (Ctx var ty, EQ var ty sym Void Void Void Void Void)
  , eq   :: Ctx var ty -> EQ var ty sym Void Void Void Void Void -> Bool
  }

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

instance (NFData var, NFData ty, NFData sym) => NFData (Typeside var ty sym) where
  rnf (Typeside tys0 syms0 eqs0 eq0) = deepseq tys0 $ deepseq syms0 $ deepseq eqs0 $ deepseq eq0 ()

typecheckTypeside :: (ShowOrdNFDataN '[var, ty, sym]) => Typeside var ty sym -> Err ()
typecheckTypeside = typeOfCol . tsToCol

-- | Converts a typeside to a collage.
tsToCol :: (Ord var, Ord ty, Ord sym) => Typeside var ty sym -> Collage var ty sym Void Void Void Void Void
tsToCol (Typeside t s e _) = Collage e' t Set.empty s Map.empty Map.empty Map.empty Map.empty
  where e' = Set.map (\(g,x)->(Map.map Left g, x)) e

data TypesideEx :: * where
  TypesideEx
    :: forall var ty sym. (ShowOrdTypeableNFDataN '[var, ty, sym]) =>
    Typeside var ty sym
    -> TypesideEx

instance NFData TypesideEx where
  rnf (TypesideEx x) = rnf x

deriving instance Show TypesideEx

------------------------------------------------------------------------------------------------------------
-- Literal typesides

type Ty  = String
type Sym = String
type Var = String

data TypesideRaw' = TypesideRaw'
  { tsraw_tys     :: [String]
  , tsraw_syms    :: [(String, ([String], String))]
  , tsraw_eqs     :: [([(String, Maybe String)], RawTerm, RawTerm)]
  , tsraw_options :: [(String, String)]
  , tsraw_imports :: [TypesideExp]
  } deriving (Eq, Show)

evalTypesideRaw :: Options -> TypesideRaw' -> [TypesideEx] -> Err TypesideEx
evalTypesideRaw ops t a' = do
  a <- doImports a'
  r <- evalTypesideRaw' t a
  l <- toOptions ops $ tsraw_options t
  p <- createProver (tsToCol r) l
  pure $ TypesideEx $ Typeside (tys r) (syms r) (eqs r) (f p)
  where
    f p ctx = prove p (Map.map Left ctx)
    doImports :: forall var ty sym. (Typeable var, Typeable ty, Typeable sym) => [TypesideEx] -> Err [Typeside var ty sym]
    doImports [] = return []
    doImports ((TypesideEx ts):r) = case cast ts of
      Nothing  -> Left "Bad import"
      Just ts' -> do { r'  <- doImports r ; return $ ts' : r' }

evalTypesideRaw' :: TypesideRaw'  -> [Typeside Var Ty Sym] -> Err (Typeside Var Ty Sym)
evalTypesideRaw' (TypesideRaw' ttys tsyms teqs _ _) is = do
  tys'  <- fromList''  ttys
  syms' <- toMapSafely   tsyms
  eqs'  <- evalEqs (addImportedSyms syms') teqs
  return $ Typeside (Set.union imported_tys' tys') (addImportedSyms syms') (Set.union imported_eqs eqs') undefined -- leave prover blank
  where
    imported_tys' = foldr Set.union Set.empty $ fmap tys is
    addImportedSyms syms' = foldr (\(f',(s,t)) m -> Map.insert f' (s,t) m) syms' $ concatMap (Map.toList . syms) is
    imported_eqs = foldr Set.union Set.empty $ fmap eqs is
    evalEqs _ [] = pure $ Set.empty
    evalEqs syms' ((ctx, lhs, rhs):eqs') = do
      ctx' <- check syms' ctx lhs rhs
      lhs' <- evalTerm syms' ctx' lhs
      rhs' <- evalTerm syms' ctx' rhs
      rest <- evalEqs syms' eqs'
      pure $ Set.insert (ctx', EQ (lhs', rhs')) rest
    evalTerm _ ctx (RawApp v []) | Map.member v ctx = pure $ Var v
    evalTerm syms' ctx (RawApp v l) = do { l' <- mapM (evalTerm syms' ctx) l ; pure $ Sym v l' }
    check _ [] _ _ = pure Map.empty
    check syms' ((v,t):l) lhs rhs = do {x <- check syms' l lhs rhs; t' <- infer v t syms' lhs rhs; pure $ Map.insert v t' x}
    infer _ (Just t) _ _ _  = return t
    infer v _ syms' lhs rhs = case (t1s, t2s) of
      (t1 : [], t2 : []) -> if t1 == t2 then return t1 else Left $ "Type mismatch on " ++ show v ++ " in " ++ show lhs ++ " = " ++ show rhs ++ ", types are " ++ show t1 ++ " and " ++ show t2
      (t1 : t2 : _, _) -> Left $ "Conflicting types for " ++ show v ++ " in " ++ show lhs ++ ": " ++ show t1 ++ " and " ++ show t2
      (_, t1 : t2 : _) -> Left $ "Conflicting types for " ++ show v ++ " in " ++ show rhs ++ ": " ++ show t1 ++ " and " ++ show t2
      ([], t : []) -> return t
      (t : [], []) -> return t
      ([], []) -> Left $ "Ambiguous variable: " ++ show v
      where
        t1s = nub $ typesOf v syms' lhs
        t2s = nub $ typesOf v syms' rhs
    typesOf _ _     (RawApp _  []) = []
    typesOf v syms' (RawApp f' as) = concatMap fn $ zip as $ maybe [] fst $ Map.lookup f' syms'
      where
        fn (a',t) = case a' of
          RawApp v' [] -> if v == v' then [t] else []
          RawApp _ _   -> typesOf v syms' a'

-----------------------------------------------------------------------------------------------------------
-- Simple typesides

initialTypeside :: Typeside Void Void Void
initialTypeside = Typeside Set.empty Map.empty Set.empty (\_ _ -> error "Impossible, please report.") --todo: use absurd

sqlTypeside :: Typeside Void String Void
sqlTypeside = Typeside (Set.fromList sqlTypeNames) Map.empty Set.empty (\_ (EQ (l, r)) -> l == r)

sqlTypeNames :: [String]
sqlTypeNames =
  [ "Bigint", "Binary", "Bit", "Blob", "Bool", "Boolean"
  , "Char", "Clob" , "Custom"
  , "Date", "Decimal", "Dom", "Double", "Doubleprecision"
  , "Float"
  , "Int", "Integer"
  , "Longvarbinary", "Longvarchar"
  , "Numeric", "Nvarchar"
  , "Other"
  , "Real"
  , "Smallint", "String"
  , "Text", "Time", "Timestamp", "Tinyint"
  , "Varbinary", "Varchar" ]

-----------------------------------------------------------------------------------------------------------
-- Expression syntax

-- there are practical haskell type system related reasons to not want this to be a gadt
data TypesideExp where
  TypesideVar :: String -> TypesideExp
  TypesideInitial :: TypesideExp
  TypesideRaw :: TypesideRaw' -> TypesideExp
  TypesideSql :: TypesideExp

deriving instance Eq TypesideExp
deriving instance Show TypesideExp

instance Deps TypesideExp where
  deps x = case x of
    TypesideVar v                        -> [(v, TYPESIDE)]
    TypesideInitial                      -> []
    TypesideSql                          -> []
    TypesideRaw (TypesideRaw' _ _ _ _ i) -> concatMap deps i


getOptionsTypeside :: TypesideExp -> [(String, String)]
getOptionsTypeside x = case x of
  TypesideSql                          -> []
  TypesideVar _                        -> []
  TypesideInitial                      -> []
  TypesideRaw (TypesideRaw' _ _ _ o _) -> o
