{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}
 
module Language.Schema where
import Prelude hiding (EQ)	
import Data.Set as Set	
import Data.Map.Strict as Map
import Language.Common
import Language.Term
import Data.Void
import Language.Typeside


data SchemaExp where
  SchemaVar :: String -> SchemaExp 
  SchemaInitial :: TypesideExp -> SchemaExp 
  SchemaCoProd  :: SchemaExp -> SchemaExp -> SchemaExp 
  SchemaRaw :: SchemaExpRaw' -> SchemaExp
                


validateSchema :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord fk, Ord att, Show fk, Show att, Show en, Ord en) => Schema var ty en sym fk att -> Err ()
validateSchema = typeOfCol . schToCol
  
schToCol :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en, Show en, Ord fk, Show fk, Ord att, Show att) => Schema var ty sym en fk att -> Collage (()+var) ty sym en fk att Void Void
schToCol (Schema ts ens fks atts path_eqs obs_eqs _) = 
 Collage (Set.union e3 $ Set.union e1 e2) (ctys tscol) 
  ens (csyms tscol) fks atts Map.empty Map.empty
   where tscol = tsToCol ts
         e1 = Set.map (\(en, EQ (l,r))->(Map.fromList [(Left (),Right en)], EQ (up3 l, up3 r))) path_eqs
         e2 = Set.map (\(en, EQ (l,r))->(Map.fromList [(Left (),Right en)], EQ (up2 l, up2 r))) obs_eqs
         e3 = Set.map (\(g,EQ (l,r))->(up1Ctx g, EQ (up1 l, up1 r))) $ ceqs tscol
         
   
up2 :: Term () ty sym en fk att Void Void -> Term (()+var) ty sym en fk att x y
up2 (Var v) = Var $ Left () 
up2 (Sym f x) = Sym f $ Prelude.map up2 x
up2 (Fk f a) = Fk f $ up2 a   
up2 (Att f a) = Att f $ up2 a 
up2 (Gen f) = absurd f   
up2 (Sk f) = absurd f    
     
         
up3 :: Term () Void Void en fk Void Void Void -> Term (()+var) ty sym en fk att x y
up3 (Var v) = Var $ Left () 
up3 (Sym f x) = absurd f
up3 (Fk f a) = Fk f $ up3 a   
up3 (Att f a) = absurd f 
up3 (Gen f) = absurd f   
up3 (Sk f) = absurd f      
     
up1 :: Term var ty sym Void Void Void Void Void -> Term (()+var) ty sym en fk att x y
up1 (Var v) = Var $ Right v 
up1 (Sym f x) = Sym f $ Prelude.map up1 x
up1 (Fk f a) = absurd f   
up1 (Att f a) = absurd f 
up1 (Gen f) = absurd f   
up1 (Sk f) = absurd f   

up1Ctx :: (Ord var) => Ctx var (ty+Void) -> Ctx (()+var) (ty+x)
up1Ctx g = Map.map (\x -> case x of 
  Left ty -> Left ty 
  Right v -> absurd v) $ Map.mapKeys Right g

  

data SchemaExpRaw' = SchemaExpRaw' {
    schraw_ens  :: [String]
  , schraw_fks :: [(String, (String, String))]
  , schraw_atts:: [(String, (String, String))]
  , schraw_peqs  :: [(String, [String])] 
  , schraw_oeqs  :: [(String, (String, String, RawTerm))] 
  , schraw_options :: [(String, String)]
} deriving (Eq, Show)

data Schema var ty sym en fk att
  = Schema
  { typeside :: Typeside var ty sym
  , ens      :: Set en
  , fks      :: Map fk (en, en)
  , atts     :: Map att (en, ty)
  , path_eqs :: Set (en, EQ () Void Void en fk Void Void Void)
  , obs_eqs  :: Set (en, EQ () ty   sym  en fk att  Void Void)
  , eq       :: en -> EQ () ty sym en fk att Void Void -> Bool
  }


data SchemaEx :: * where
  SchemaEx :: forall var ty sym en fk att. Schema var ty sym en fk att -> SchemaEx

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att)
  => Eq (Schema var ty sym en fk att) where
  (==) (Schema ts  ens  fks  atts  path_eqs  obs_eqs  eq)
       (Schema ts' ens' fks' atts' path_eqs' obs_eqs' eq')
    =  (ens == ens') && (fks == fks') && (atts == atts')
    && (path_eqs == path_eqs') && (obs_eqs == obs_eqs')
    && (ts == ts')

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att)
  => Show (Schema var ty sym en fk att) where
  show (Schema ts ens fks atts path_eqs obs_eqs eq) =
    "ens = " ++ (show ens) ++
    "\nfks = " ++ (show fks) ++ "\natts = " ++ (show atts) ++
    "\npath_eqs = " ++ (show path_eqs) ++ "\nobs_eqs = " ++ (show obs_eqs)
