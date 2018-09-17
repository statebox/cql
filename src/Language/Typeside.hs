{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}
 
module Language.Typeside where
import Prelude hiding (EQ)	
import Data.Set as Set	
import Data.Map.Strict as Map
import Language.Common
import Language.Term
import Data.Void
import Language.Prover
import Data.List (intercalate)
--  Semantics -----------------------------------------------------------------
  
 

fromList'' :: (Show k, Ord k) => [k] -> Err (Set k) 
fromList'' (k:l) = do l' <- fromList'' l 
                      if Set.member k l' 
                      then Left $ "Duplicate binding: " ++ (show k)
                      else pure $ Set.insert k l' 
   
fromList' :: (Show k, Ord k) => [(k,v)] -> Err (Map k v) 
fromList' ((k,v):l) = do l' <- fromList' l 
                         if Map.member k l' 
                         then Left $ "Duplicate binding: " ++ (show k)
                         else pure $ Map.insert k v l'

deps (TypesideVar v) = [(v, TYPESIDE)]
deps TypesideInitial = []
deps (TypesideRaw r) = []

data Typeside var ty sym
  = Typeside
  { tys  :: Set ty
  , syms :: Map sym ([ty], ty)
  , eqs  :: Set (Ctx var ty, EQ var ty sym Void Void Void Void Void)
  , eq   :: Ctx var ty -> EQ var ty sym Void Void Void Void Void -> Bool

  {-- since we're in Haskell, a different DSL embedding strategy might be called for than the java version
  , hakell_tys   :: Map ty String
  , haskell_syms :: Map sym String
  --}
  }


data TypesideEx :: * where  
 TypesideEx :: forall var ty sym. Typeside var ty sym -> TypesideEx
 
instance (Eq var, Eq ty, Eq sym) => Eq (Typeside var ty sym) where
  (==) (Typeside tys  syms  eqs  eq)
       (Typeside tys' syms' eqs' eq')
    = (tys == tys') && (syms == syms') && (eqs == eqs')

instance (Show var, Show ty, Show sym) => Show (Typeside var ty sym) where
  show (Typeside tys syms eqs eq) =
    "tys = "    ++ show tys ++
    "\nsyms = " ++ show syms ++
    "\neqs = "  ++ show eqs

--instance Semantics (Typeside var ty sym) where
validateTypeside :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym) => Typeside var ty sym -> Err ()
validateTypeside = typeOfCol . tsToCol
 
--todo: make validating Typeside function

--todo: parser should target these
data TypesideRaw' = TypesideRaw' {
--  tsraw_imports :: [TypesideExp -> Either String TypesideEx]  these are going to be nasty bc of the type system
   tsraw_tys  :: [String]
  , tsraw_syms :: [(String, ([String], String))]
  , tsraw_eqs  :: [([(String, String)], RawTerm, RawTerm)] 
  , tsraw_options :: [(String, String)]
} deriving (Eq, Show)

tsToCol :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym) => Typeside var ty sym -> Collage var ty sym Void Void Void Void Void
tsToCol (Typeside t s e _) = Collage e' t Set.empty s Map.empty Map.empty Map.empty Map.empty
 where e' = Set.map (\(g,x)->(Map.map Left g, x)) e


evalTypesideRaw :: TypesideRaw' -> Err TypesideEx
evalTypesideRaw t = 
 do r <- evalTypesideRaw' t
    o <- fromList' $ tsraw_options t
    n <- proverStringToName o
    p <- createProver n (tsToCol r)   
    pure $ TypesideEx $ Typeside (tys r) (syms r) (eqs r) (f p)
 where 
  f p ctx eq = prove p (Map.map Left ctx) eq    

evalTypesideRaw' :: TypesideRaw' -> Err (Typeside String String String)
evalTypesideRaw' (TypesideRaw' tys syms eqs ops) = 
  do tys' <- fromList'' tys
     syms' <- fromList' syms 
     eqs' <- f syms' eqs
     pure $ Typeside tys' syms' eqs' undefined -- leave prover blank
 where f syms' [] = pure $ Set.empty
       f syms' ((ctx, lhs, rhs):eqs') = do ctx' <- check ctx
                                           lhs' <- g syms' ctx' lhs  
                                           rhs' <- g syms' ctx' rhs
                                           rest <- f syms' eqs'
                                           pure $ Set.insert (ctx', EQ (lhs', rhs')) rest
       g syms' ctx (RawApp v []) | Map.member v ctx = pure $ Var v 
       g syms' ctx (RawApp v l) = do l' <- mapM (g syms' ctx) l
                                     pure $ Sym v l'        
       check [] = pure Map.empty
       check ((v,t):l) = if elem v tys then do {x <- check l; pure $ Map.insert v t x} else Left $ "Not a type: " ++ (show t)                                  


-- there are practical haskell type system related reasons to not want this to be a gadt 
data TypesideExp where
  TypesideVar :: String -> TypesideExp
  TypesideInitial :: TypesideExp 
  TypesideRaw :: TypesideRaw' -> TypesideExp
  
 
deriving instance Eq TypesideExp
deriving instance Show TypesideExp
