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
import Language.Options
import Language.Prover
import Data.Typeable
import Data.List (intercalate)


data SchemaExp where
  SchemaVar :: String -> SchemaExp
  SchemaInitial :: TypesideExp -> SchemaExp
  SchemaCoProd  :: SchemaExp -> SchemaExp -> SchemaExp
  SchemaRaw :: SchemaExpRaw' -> SchemaExp
 deriving Show


typecheckSchema :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord fk, Ord att, Show fk, Show att, Show en, Ord en)
 => Schema var ty sym en fk att -> Err (Schema var ty sym en fk att)
typecheckSchema t = do x <- typeOfCol $ schToCol  t
                       return t

schToCol :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en, Show en, Ord fk, Show fk, Ord att, Show att) => Schema var ty sym en fk att -> Collage (()+var) ty sym en fk att Void Void
schToCol (Schema ts ens' fks' atts' path_eqs' obs_eqs' _) =
 Collage (Set.union e3 $ Set.union e1 e2) (ctys tscol)
  ens' (csyms tscol) fks' atts' Map.empty Map.empty
   where tscol = tsToCol ts
         e1 = Set.map (\(en, EQ (l,r))->(Map.fromList [(Left (),Right en)], EQ (up3 l, up3 r))) path_eqs'
         e2 = Set.map (\(en, EQ (l,r))->(Map.fromList [(Left (),Right en)], EQ (up2 l, up2 r))) obs_eqs'
         e3 = Set.map (\(g,EQ (l,r))->(up1Ctx g, EQ (up1 l, up1 r))) $ ceqs tscol


up2 :: Term () ty sym en fk att Void Void -> Term (()+var) ty sym en fk att x y
up2 (Var _) = Var $ Left ()
up2 (Sym f x) = Sym f $ Prelude.map up2 x
up2 (Fk f a) = Fk f $ up2 a
up2 (Att f a) = Att f $ up2 a
up2 (Gen f) = absurd f
up2 (Sk f) = absurd f


up3 :: Term () Void Void en fk Void Void Void -> Term (()+var) ty sym en fk att x y
up3 (Var _) = Var $ Left ()
up3 (Sym f _) = absurd f
up3 (Fk f a) = Fk f $ up3 a
up3 (Att f _) = absurd f
up3 (Gen f) = absurd f
up3 (Sk f) = absurd f

up4' :: z -> Term () ty sym en fk att x y -> Term z ty sym en fk att x y
up4' z (Var _) = Var $ z
up4' z (Sym f as) = Sym f $ Prelude.map (up4' z) as
up4' z (Fk f a) = Fk f $ up4' z a
up4' z (Att f a) = Att f $ up4' z a
up4' z (Gen f) = Gen f
up4' z (Sk f) = Sk f

up1 :: Term var ty sym Void Void Void Void Void -> Term (()+var) ty sym en fk att x y
up1 (Var v) = Var $ Right v
up1 (Sym f x) = Sym f $ Prelude.map up1 x
up1 (Fk f _) = absurd f
up1 (Att f _) = absurd f
up1 (Gen f) = absurd f
up1 (Sk f) = absurd f


up0 :: Term var ty sym Void Void Void Void Void -> Term var ty sym en fk att x y
up0 (Var v) = Var v
up0 (Sym f x) = Sym f $ Prelude.map up0 x
up0 (Fk f _) = absurd f
up0 (Att f _) = absurd f
up0 (Gen f) = absurd f
up0 (Sk f) = absurd f

up1Ctx :: (Ord var) => Ctx var (ty+Void) -> Ctx (()+var) (ty+x)
up1Ctx g = Map.map (\x -> case x of
  Left ty -> Left ty
  Right v -> absurd v) $ Map.mapKeys Right g



data SchemaExpRaw' = SchemaExpRaw' {
    schraw_ts :: TypesideExp
  , schraw_ens  :: [String]
  , schraw_fks :: [(String, (String, String))]
  , schraw_atts:: [(String, (String, String))]
  , schraw_peqs  :: [([String], [String])]
  , schraw_oeqs  :: [(String, String, RawTerm, RawTerm)]
  , schraw_options :: [(String, String)]
} deriving (Eq, Show)

sch_fks = fks
sch_atts = atts

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

type En = String
type Fk = String
type Att = String

conv :: (Typeable ty,Show ty) => [(String, (String, String))] -> Err [(String, (String, ty))]
conv [] = pure []
conv ((att,(en,ty)):tl) = case cast ty of 
   Just ty' -> do x <- conv tl
                  return $ (att,(en,ty')):x
   Nothing -> Left $ "Not a type "   


evalSchemaRaw' :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Typeable sym, Typeable ty) 
 => Typeside var ty sym -> SchemaExpRaw' -> Err (Schema var ty sym En Fk Att)
evalSchemaRaw' (x@(Typeside tys sym eqs _)) (SchemaExpRaw' ts ens fks atts peqs oeqs ops) = 
  do fks' <- toMapSafely fks 
     cc <- conv atts
     atts' <- toMapSafely cc 
     peqs' <- k peqs
     oeqs' <- f oeqs 
     typecheckSchema $ Schema x (Set.fromList ens) fks' atts' peqs' oeqs' undefined --leave prover blank
 where     
  keys = fst . unzip 
  --f :: [(String, String, RawTerm, RawTerm)] -> Err (Set (En, EQ () ty   sym  en fk att  Void Void))
  f [] = pure $ Set.empty
  f ((v, en, lhs, rhs):eqs') = do ctx' <- return $ Map.fromList [((),en)] 
                                  lhs' <- return $ g v (keys fks) (keys atts) lhs
                                  rhs' <- return $ g v (keys fks) (keys atts) rhs
                                  rest <- f eqs'
                                  pure $ Set.insert (en, EQ (lhs', rhs')) rest
  g' :: String ->[String]-> [String] -> RawTerm-> Term () Void Void en Fk Void  Void Void                                 
  g' v fks atts (RawApp x []) | v == x = Var ()
  g' v fks atts (RawApp x (a:[])) | elem x fks = Fk x $ g' v fks atts a 
  g :: Typeable sym => String ->[String]-> [String] -> RawTerm-> Term () ty sym en Fk Att  Void Void                                   
  g v fks atts (RawApp x []) | v == x = Var ()
  g v fks atts (RawApp x (a:[])) | elem x fks = Fk x $ g' v fks atts a 
  g v fks atts (RawApp x (a:[])) | elem x atts = Att x $ g' v fks atts a 
  g u fks atts (RawApp v l) = let l' = Prelude.map (g u fks atts) l
                              in case cast v of
                                  Just x -> Sym x l'
                                  Nothing -> error "impossible until complex typesides"   
  h :: [String] -> [String] -> Term () Void Void En Fk Void Void Void                           
  h ens (s:ex) | elem s ens = h ens ex
  h ens (s:ex) | otherwise = Fk s $ h ens ex
  h ens [] = Var ()
  --k :: [([String], [String])] -> Err (Set (En, EQ () Void Void en fk Void Void Void))
  k [] = pure $ Set.empty
  k ((l,r):eqs') = do lhs' <- return $ h ens $ reverse l
                      rhs' <- return $ h ens $ reverse r
                      en <- findEn ens fks l
                      ctx' <- return $ Map.fromList [((),en)] 
                      rest <- k eqs'
                      pure $ Set.insert (en, EQ (lhs', rhs')) rest
  findEn ens fks (s:ex) | elem s ens = return s
  findEn ens fks (s:ex) | Map.member s (Map.fromList fks) = return $ fst $ fromJust $ Prelude.lookup s fks 
  findEn ens fks (s:ex) | otherwise = findEn ens fks ex
  findEn ens fks [] = Left "Path equation cannot be typed"
  
                                        


evalSchemaRaw :: (Ord var, Ord ty, Ord sym, Typeable sym, Typeable ty, Show var, Show ty, Show sym) 
 => Typeside var ty sym -> SchemaExpRaw' -> Err SchemaEx
evalSchemaRaw ty t =
 do r <- evalSchemaRaw' ty t 
    l <- toOptions $ schraw_options t
    p <- createProver (schToCol r) l
    pure $ SchemaEx $ Schema ty (ens r) (fks r) (atts r) (path_eqs r) (obs_eqs r) (f p)
 where
  f p en (EQ (l,r)) = prove p (Map.fromList [(Left (),Right en)]) (EQ (up8 l, up8 r))
  


up8 :: Term () ty sym En Fk Att Void Void -> Term (() + var) ty sym En Fk Att Void Void 
up8 (Var v) = Var $ Left v
up8 (Sym f as) = Sym f $ Prelude.map up8 as
up8 (Fk f a) = Fk f $ up8' a
up8 (Att f a) = Att f $ up8' a
up8 (Gen g) = absurd g
up8 (Sk s) = absurd s

up8' :: Term () Void Void En Fk Void Void Void -> Term (() + var) Void Void En Fk Void Void Void 
up8' (Var v) = Var $ Left v
up8' (Sym f as) = absurd f
up8' (Fk f a) = Fk f $ up8' a
up8' (Att f a) = Att f $ up8' a
up8' (Gen g) = absurd g
up8' (Sk s) = absurd s 

data SchemaEx :: * where
  SchemaEx :: forall var ty sym en fk att. 
    (Show var, Show ty, Show sym, Show en, Show fk, Show att, Typeable sym, Typeable ty, Typeable fk, Typeable att, Typeable en, Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att) =>
    Schema var ty sym en fk att -> SchemaEx

deriving instance Show (SchemaEx)     

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att)
  => Eq (Schema var ty sym en fk att) where
  (==) (Schema ts'  ens'  fks'  atts'  path_eqs'  obs_eqs'  _)
       (Schema ts'' ens'' fks''  atts'' path_eqs'' obs_eqs'' _)
    =  (ens' == ens'') && (fks' == fks'') && (atts' == atts'')
    && (path_eqs' == path_eqs'') && (obs_eqs' == obs_eqs'')
    && (ts' == ts'')

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att)
  => Show (Schema var ty sym en fk att) where
  show (Schema _ ens' fks' atts' path_eqs' obs_eqs' _) = "schema {\n" ++
    "entities\n\t"  ++ intercalate "\n\t" (Prelude.map show $ Set.toList ens') ++
    "\nforeign_keys\n\t" ++ intercalate "\n\t" fks'' ++ 
    "\natts\n\t" ++ intercalate "\n\t" atts'' ++
    "\npath_equations\n\t" ++ intercalate "\n\t" (eqs'' path_eqs') ++ 
    "\nobservation_equations\n\t " ++ intercalate "\n\t" (eqs'' obs_eqs') ++ " }"
   where fks'' = Prelude.map (\(k,(s,t)) -> show k ++ " : " ++ show s ++ " -> " ++ show t) $ Map.toList fks' 
         atts'' = Prelude.map (\(k,(s,t)) -> show k ++ " : " ++ show s ++ " -> " ++ show t) $ Map.toList atts'
         eqs'' x  = Prelude.map (\(en,EQ (l,r)) -> "forall x : " ++ show en ++ " . " ++ show (up4' "x" l) ++ " = " ++ show (up4' "x" r)) $ Set.toList x

   

