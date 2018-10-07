{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Mapping where
import Prelude hiding (EQ)
import Data.Map.Strict as Map
import Language.Term
import Language.Schema as X
import Data.Void
import Language.Common
import Data.Typeable
import Language.Options
import Data.Set as Set
import Data.Maybe
import Data.List

 

data Mapping var ty sym en fk att en' fk' att'
  = Mapping
  { src  :: Schema var ty sym en  fk  att
  , dst  :: Schema var ty sym en' fk' att'

  , ens  :: Map en  en'
  , fks  :: Map fk  (Term () Void Void en' fk' Void Void Void)
  , atts :: Map att (Term () ty   sym  en' fk' att' Void Void)
  }



mapToMor (Mapping src dst ens fks atts) = Morphism (schToCol src) (schToCol dst) ens fks atts Map.empty Map.empty

data MappingEx :: * where
  MappingEx :: forall var ty sym en fk att en' fk' att'. 
   (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att') =>  
    Mapping var ty sym en fk att en' fk' att' -> MappingEx

deriving instance Show MappingEx  


instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att')
  => Show (Mapping var ty sym en fk att en' fk' att') where
  show (Mapping _ _ ens' fks' atts') = "mapping {\n" ++
    "entities\n\t"  ++ intercalate "\n\t" ens'' ++
    "\nforeign_keys\n\t" ++ intercalate "\n\t" fks'' ++ 
    "\nattributes\n\t" ++ intercalate "\n\t" atts'' ++ " }\n"
   where ens'' = Prelude.map (\(s,t) -> show s ++ " -> " ++ show t) $ Map.toList ens'
         fks'' = Prelude.map (\(k,s) -> show k ++ " -> " ++ show s) $ Map.toList fks' 
         atts'' = Prelude.map (\(k,s)-> show k ++ " -> " ++ show s) $ Map.toList atts'
         

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq en', Eq fk', Eq att')
  => Eq (Mapping var ty sym en fk att en' fk' att') where
  (Mapping s1' s2' ens' fks' atts') == (Mapping s1'' s2'' ens'' fks'' atts'')
    = (s1' == s1'') && (s2' == s2'') && (ens' == ens'') && (fks' == fks'') && (atts' == atts'')

typecheckMapping ::   (Show att, Show att', Ord var, Show var, Typeable en, Typeable en', Ord en, Show en, Show en', Typeable sym, Typeable att, Typeable fk, Show fk,
    Typeable fk', Ord att, Typeable att', Ord en, Ord att', Ord en', Ord fk', Show fk', Ord fk, Ord ty, Show ty, Show sym, Ord sym) =>
 Mapping var ty sym en fk att en' fk' att' -> Err (Mapping var ty sym en fk att en' fk' att') 
typecheckMapping m = do _ <- typeOfMor $ mapToMor m
                        _ <- validateMapping m
                        return m

validateMapping :: forall var ty sym en fk att en' fk' att' .
  (Show att, Show att', Ord var, Show var, Typeable en, Typeable en', Ord en, Show en, Show en', Typeable sym, Typeable att, Typeable fk, Show fk,
    Typeable fk', Ord att, Typeable att', Ord en, Ord att', Ord en', Ord fk', Show fk', Ord fk, Ord ty, Show ty, Show sym, Ord sym) =>
 Mapping var ty sym en fk att en' fk' att' -> Err (Mapping var ty sym en fk att en' fk' att') 
validateMapping (m@(Mapping src dst ens fks atts)) = do -- _ <- mapM f (Set.toList $ path_eqs src)
                                                        _ <- mapM f (Set.toList $ obs_eqs src)
                                                        pure m
 where f (enx, EQ (l,r)) = let l' = trans (mapToMor m) l
                               r' = trans (mapToMor m) r :: Term () ty sym en' fk' att' Void Void
                               en'= fromJust $ Map.lookup enx ens
                          in if eq dst en' (EQ ( l',  r'))
                             then pure ()
                             else Left $ show l ++ " = " ++ show r ++ " translates to " ++ show l' ++ " = " ++ show r' ++ " which is not provable" 

data MappingExp   where
  MappingVar     :: String -> MappingExp
  MappingId      :: SchemaExp -> MappingExp
  MappingRaw     :: MappingExpRaw' -> MappingExp
 deriving Show

data MappingExpRaw' = MappingExpRaw' {
    mapraw_src :: SchemaExp,
    mapraw_dst :: SchemaExp,
    mapraw_ens  :: [(String, String)]
  , mapraw_fks :: [(String, [String])]
  , mapraw_atts  :: [(String, (String, RawTerm))]
  , mapraw_options :: [(String, String)]
} deriving (Show)

--todo: combine with schema 
conv'' :: forall ty ty2. (Typeable ty,Show ty, Typeable ty2, Show ty2) => [(String, String)] -> Err [(ty2, ty)]
conv'' [] = pure []
conv'' ((ty2,ty):tl) = case cast ty :: Maybe ty of 
   Just ty' -> do x <- conv'' tl
                  case cast ty2 :: Maybe ty2 of
                    Just ty2' -> return $ (ty2', ty'):x
                    Nothing -> Left $ "Not in source schema/typeside: " ++ show ty2  
   Nothing -> Left $ "Not in target schema/typeside: " ++ show ty   

cast' :: (Typeable x, Typeable y) => x -> String -> Err y
cast' x s = case cast x of
   Nothing -> Left s
   Just y -> return y


elem' x [] = False
elem' x (a:b) = case cast x of 
  Nothing -> elem' x b 
  Just x' -> x' == a || elem' x b

evalMappingRaw' :: forall var ty sym en fk att en' fk' att' .
  (Ord var, Ord ty, Ord sym, Show att, Show att', Show sym, Show var, Show ty, Typeable en, Typeable en', Ord en, Show en, Show en', Typeable sym, Typeable att, Typeable fk, Show fk,
    Typeable fk', Ord att, Typeable att', Ord en, Ord att', Ord en', Ord fk', Show fk', Ord fk) =>
  Schema var ty sym en fk att -> Schema var ty sym en' fk' att' -> MappingExpRaw' 
 -> Err (Mapping var ty sym en fk att en' fk' att')
evalMappingRaw' src dst (MappingExpRaw' _ _ ens0 fks0 atts0 ops) = 
  do ens1 <- conv'' ens0
     ens2 <- toMapSafely ens1 
     x <- k fks0
     y <- f atts0
     typecheckMapping $ Mapping src dst ens2 x y  
 where    
  keys = fst . unzip 
  fks = Map.toList $ X.fks dst
  ens = Set.toList $ X.ens dst 
  atts = Map.toList $ X.atts dst
  f [] = pure $ Map.empty
  f  ((att, (v, t)):ts) = do t'   <- return $ g v (keys fks) (keys atts) t
                             rest <- f ts
                             att' <- cast' att $ "Not an attribute " ++ att
                             pure $ Map.insert att' t' rest
  --g' :: String ->[String]-> [String] -> RawTerm-> Term () Void Void en Fk Void  Void Void                                 
  g' v fks atts (RawApp x []) | v == x = Var ()
  g' v fks atts (RawApp x (a:[])) | elem' x fks = Fk (fromJust $ cast x) $ g' v fks atts a 
  --g :: Typeable sym => String ->[fk']-> [att'] -> RawTerm -> Term () ty sym en' fk' att' Void Void                                   
  g v fks atts (RawApp x []) | v == x = Var ()
  g v fks atts (RawApp x (a:[])) | elem' x fks = Fk (fromJust $ cast x) $ g' v fks atts a 
  g v fks atts (RawApp x (a:[])) | elem' x atts = Att (fromJust $ cast x) $ g' v fks atts a 
  g u fks atts (RawApp v l) = let l' = Prelude.map (g u fks atts) l
                              in case cast v of
                                  Just x -> Sym x l'
                                  Nothing -> error "impossible until complex typesides"   
  --h :: [en'] -> [String] -> Err (Term () Void Void en' fk' Void Void Void)                          
  h ens (s:ex) | elem' s ens = h ens ex
  h ens (s:ex) | elem' s (keys fks) = do { h' <- h ens ex ; return $ Fk (fromJust $ cast s) h' }
               | otherwise = Left $ "Not a target fk: " ++ s
  h ens [] = return $ Var ()
 -- k :: [(String, [String])] -> Err (Map fk (Term () Void Void en' fk' Void Void Void))
  k [] = pure $ Map.empty
  k ((fk,p):eqs') =do p' <- h ens $ reverse p
                      en <- findEn ens fks p
                      rest <- k eqs'
                      fk' <- cast' fk $ "Not a src fk: fk"
                      pure $ Map.insert fk' p' rest
  findEn ens fks (s:ex) | elem' s ens = return $ fromJust $ cast s
  findEn ens fks (s:ex) | elem' s (keys $ fks) = return $ fst $ fromJust $ Prelude.lookup (fromJust $ cast s) fks 
  findEn ens fks (s:ex) | otherwise = findEn ens fks ex
  findEn ens fks [] = Left "Path cannot be typed"                                 



                                        
evalMappingRaw :: (Show att', Show en, Ord sym, Show sym, Ord var, Ord ty, Ord en', Show var, Show ty, Show fk', 
   Typeable en', Typeable ty, Ord en, Typeable fk, Typeable att, Ord fk, Typeable en, Show fk, 
   Ord att, Show att, Show fk, Show en', Typeable sym, Ord fk, Show var, Typeable fk', Typeable att', Ord att',
   Ord fk' ) 
  => Schema var ty sym en fk att -> Schema var ty sym en' fk' att' -> MappingExpRaw' -> Err MappingEx
evalMappingRaw src dst t =
 do r <- evalMappingRaw' src dst t 
    --l <- toOptions $ mapraw_options t
    pure $ MappingEx r 

