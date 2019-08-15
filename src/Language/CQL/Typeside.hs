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

module Language.CQL.Typeside where
import           Control.DeepSeq
import           Data.Bifunctor        (first)
import           Data.List             (nub)
import           Data.Map.Strict       hiding (foldr)
import qualified Data.Map.Strict       as Map
import           Data.Set              (Set)
import qualified Data.Set              as Set
import           Data.Typeable
import           Data.Void
import           Language.CQL.Collage  (Collage(..), typeOfCol)
import           Language.CQL.Common
import           Language.CQL.Options
import           Language.CQL.Prover
import           Language.CQL.Term
import           Prelude               hiding (EQ)

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
  show (Typeside tys' syms' eqs' _) =
    section "typeside" $ unlines
      [ section "types"     $ unlines . fmap show $ Set.toList tys'
      , section "functions" $ unlines syms''
      , section "equations" $ unlines eqs''
      ]
   where
    syms''  = (\(k,(s,t)) -> show k ++ " : " ++ show s ++ " -> " ++ show t) <$> Map.toList syms'
    eqs''   = (\(k,s)     -> "forall " ++ showCtx k ++ " . " ++ show s)     <$> Set.toList eqs'

    showCtx :: (Show a1, Show a2) => Map a1 a2 -> String
    showCtx m = unwords $ fmap (sepTup " : ") $ Map.toList m

instance (NFData var, NFData ty, NFData sym) => NFData (Typeside var ty sym) where
  rnf (Typeside tys0 syms0 eqs0 eq0) = deepseq tys0 $ deepseq syms0 $ deepseq eqs0 $ deepseq eq0 ()

typecheckTypeside :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym]) => Typeside var ty sym -> Err ()
typecheckTypeside = typeOfCol . tsToCol

-- | Converts a typeside to a collage.
tsToCol :: (Ord var, Ord ty, Ord sym) => Typeside var ty sym -> Collage var ty sym Void Void Void Void Void
tsToCol (Typeside tys syms eqs _) =
  Collage (leftify eqs) tys Set.empty syms mempty mempty mempty mempty
  where
    leftify = Set.map (first (fmap Left))

data TypesideEx :: * where
  TypesideEx
    :: forall var ty sym. (MultiTyMap '[Show, Ord, Typeable, NFData] '[var, ty, sym])
    => Typeside var ty sym
    -> TypesideEx

instance NFData TypesideEx where
  rnf (TypesideEx x) = rnf x

-- TypesideEx is an implementation detail, so hide its presence
instance (Show TypesideEx) where
  show (TypesideEx i) = show i

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
evalTypesideRaw opts tsRaw imports = do
  imports' <- doImports imports
  ts       <- evalTypesideRaw' tsRaw imports'
  opts'    <- toOptions opts $ tsraw_options tsRaw
  prover   <- createProver (tsToCol ts) opts'
  let eq   =  \ctx -> prove prover (Map.map Left ctx)
  pure $ TypesideEx $ Typeside (tys ts) (syms ts) (eqs ts) eq
  where
    doImports :: forall var ty sym. (Typeable var, Typeable ty, Typeable sym) => [TypesideEx] -> Err [Typeside var ty sym]
    doImports []                    = return []
    doImports (TypesideEx imp:imps) = do
      imp'  <- note "Bad import" $ cast imp
      imps' <- doImports imps
      return $ imp' : imps'

evalTypesideRaw' :: TypesideRaw' -> [Typeside Var Ty Sym] -> Err (Typeside Var Ty Sym)
evalTypesideRaw' (TypesideRaw' ttys tsyms teqs _ _) importedTys = do
  tys'  <- toSetSafely ttys
  syms' <- toMapSafely tsyms
  eqs'  <- evalEqs (addImportedSyms syms') teqs
  return $ Typeside (Set.union importedTys' tys') (addImportedSyms syms') (Set.union importedEqs eqs') prover
  where
    prover                = undefined -- intentionally left blank; is there a less explosive way to do this?
    importedTys'          = foldMap tys importedTys
    importedEqs           = foldMap eqs importedTys
    addImportedSyms syms' = foldr (\(f',(s,t)) m -> Map.insert f' (s,t) m) syms' $ concatMap (Map.toList . syms) importedTys

    evalEqs _ [] = pure Set.empty
    evalEqs syms' ((ctx, lhs, rhs):eqs') = do
      ctx' <- check    syms' ctx  lhs rhs
      lhs' <- evalTerm syms' ctx' lhs
      rhs' <- evalTerm syms' ctx' rhs
      rest <- evalEqs  syms' eqs'
      pure $ Set.insert (ctx', EQ (lhs', rhs')) rest

    evalTerm :: Monad m => t -> Ctx String a -> RawTerm -> m (Term String ty String en fk att gen sk)
    evalTerm _     ctx (RawApp v []) | Map.member v ctx = pure $ Var v
    evalTerm syms' ctx (RawApp v l)                     = Sym v <$> mapM (evalTerm syms' ctx) l

    check _ [] _ _ = pure Map.empty
    check syms' ((v,t):l) lhs rhs = do {x <- check syms' l lhs rhs; t' <- infer v t syms' lhs rhs; pure $ Map.insert v t' x}

    infer _ (Just t) _ _ _  = return t
    infer v _ syms' lhs rhs = case (t1s, t2s) of
      ([t1]       , [t2]       ) -> if t1 == t2 then return t1 else Left $ "Type mismatch on " ++ show v ++ " in " ++ show lhs ++ " = " ++ show rhs ++ ", types are " ++ show t1 ++ " and " ++ show t2
      (t1 : t2 : _, _          ) -> Left $ "Conflicting types for " ++ show v ++ " in " ++ show lhs ++ ": " ++ show t1 ++ " and " ++ show t2
      (_          , t1 : t2 : _) -> Left $ "Conflicting types for " ++ show v ++ " in " ++ show rhs ++ ": " ++ show t1 ++ " and " ++ show t2
      ([]         , [t]        ) -> return t
      ([t]        , []         ) -> return t
      ([]         , []         ) -> Left $ "Ambiguous variable: " ++ show v
      where
        t1s = nub $ typesOf v syms' lhs
        t2s = nub $ typesOf v syms' rhs

    typesOf _ _     (RawApp _  []) = []
    typesOf v syms' (RawApp f' as) = concatMap fn $ zip as $ maybe [] fst $ Map.lookup f' syms'
      where
        fn (a',t) = case a' of
          RawApp v' [] -> [t | v == v']
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
  , "Varbinary", "Varchar"
  ]

-----------------------------------------------------------------------------------------------------------
-- Expression syntax

-- There are practical haskell type system related reasons to not want this to be a GADT.
data TypesideExp where
  TypesideVar     :: String       -> TypesideExp
  TypesideInitial ::                 TypesideExp
  TypesideRaw     :: TypesideRaw' -> TypesideExp
  TypesideSql     ::                 TypesideExp

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
