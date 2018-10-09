{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Instance where
import Prelude hiding (EQ)
import Data.Set as Set
import Data.Map.Strict as Map 
import Data.List
import Language.Common
import Language.Term as Term
import Language.Typeside as Typeside 
import Language.Schema as Schema
import Language.Mapping 
import Language.Query 
import Data.Void 
import Data.Typeable hiding (typeOf)
import Language.Prover 
import Language.Options
import Debug.Trace
import Data.Maybe

--------------------------------------------------------------------------------

emptyInstance :: Schema var ty sym en fk att -> Instance var ty sym en fk att Void Void Void Void
emptyInstance ts'' = Instance ts'' (Presentation Map.empty Map.empty Set.empty) 
                              (\_ -> undefined) $ Algebra ts''
                                                     (\x -> Set.empty) (\x -> undefined) (\x -> undefined)
                                                      (\x -> Set.empty) (\x -> undefined) (\x -> undefined)
                                                        Set.empty

typecheckPresentation :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord fk, Ord att, Show fk, Show att, Show en, Ord en, Ord gen, Show gen, Ord sk, Show sk) 
 => Schema var ty sym en fk att -> Presentation var ty sym en fk att gen sk -> Err (Presentation var ty sym en fk att gen sk)
typecheckPresentation sch p = do x <- typeOfCol $ instToCol sch p
                                 return p

data Algebra var ty sym en fk att gen sk x y
  = Algebra { 
   aschema :: Schema var ty sym en fk att

  , en    :: en -> (Set x) -- globally unique xs
  , nf    :: Term Void Void Void en fk Void gen Void -> x
  , repr  :: x -> Term Void Void Void en fk Void gen Void

  , ty    :: ty -> (Set y) -- globally unique ys
  , nf'   :: sk + (x, att) -> Term Void ty sym Void Void Void Void y

  , repr' :: y -> Term Void ty sym en fk att gen sk
  , teqs  :: Set (EQ Void ty sym Void Void Void Void y)

  } -- omit Eq, doesn't seem to be necessary for now

appearsIn :: Eq y => y -> Term Void ty sym Void Void Void Void y -> Bool
appearsIn y (Sk y') | y == y' = True
                    | otherwise = False
appearsIn y (Fk f a) = absurd f
appearsIn y (Att f a) = absurd f
appearsIn y (Gen g) = False
appearsIn y (Sym f as) = or (Prelude.map (appearsIn y) as)


findGen :: Eq y => Set (EQ Void ty sym Void Void Void Void y) -> Maybe (y, Term Void ty sym Void Void Void Void y)
findGen = f . Set.toList
 where g (Sk y) t = if appearsIn y t then Nothing else Just (y, t)
       f [] = Nothing
       f ((EQ (lhs, rhs)):tl) = case g lhs rhs of 
          Nothing -> case g rhs lhs of 
            Nothing -> f tl
            Just (y, r) -> Just (y, r)
          Just (y, r) -> Just (y, r) 


replace :: Eq y => y -> Term Void ty sym Void Void Void Void y -> Term Void ty sym Void Void Void Void y -> Term Void ty sym Void Void Void Void y
replace toReplace replacer (Sk s) = if (s == toReplace) then replacer else Sk s
replace toReplace replacer (Sym f a) = Sym f $ Prelude.map (replace toReplace replacer) a

simplify' :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk, Ord x, Show x, Ord y, Show y) => 
 Algebra var ty sym en fk att gen sk x y -> Algebra var ty sym en fk att gen sk x y
simplify' alg = case simplify alg of 
  Nothing -> alg 
  Just alg' -> simplify' alg'

simplify :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk, Ord x, Show x, Ord y, Show y) => 
 Algebra var ty sym en fk att gen sk x y -> Maybe (Algebra var ty sym en fk att gen sk x y)
simplify (Algebra sch en nf repr ty nf' repr' teqs) = case findGen teqs of
  Nothing -> Nothing
  Just (toRemove, replacer) -> let teqs2 = Set.map (\(EQ (lhs, rhs)) -> EQ (replace toRemove replacer lhs, replace toRemove replacer rhs)) teqs
                                   ty2 t = Set.delete toRemove (ty t)
                                   nf2 e = replace toRemove replacer $ nf' e
                                   repr2 = repr' 
                 in Just $ Algebra sch en nf repr ty2 nf2 repr2 teqs2
 --where gens = reifyGens en $ ens sch 

castX :: Term Void ty sym en fk att gen sk -> Maybe (Term Void Void Void en fk Void gen Void)
castX (Gen g) = Just $ Gen g
castX (Fk f a) = do { x <- castX a ; Just $ Fk f $ x } 
castX (Var v) = absurd v
castX _ = Nothing
       
nf'' :: Algebra var ty sym en fk att gen sk x y -> Term Void ty sym en fk att gen sk -> Term Void ty sym Void Void Void Void y 
nf'' alg (Sym f as) = Sym f $ Prelude.map (nf'' alg) as
nf'' alg (Att f a) = nf' alg $ Right (nf alg (fromJust $ castX a), f) 

aGen :: Algebra var ty sym en fk att gen sk x y -> gen -> x
aGen alg g = nf alg $ Gen g

aFk :: Algebra var ty sym en fk att gen sk x y -> fk -> x -> x
aFk alg f x = nf alg $ Fk f $ repr alg x

aAtt :: Algebra var ty sym en fk att gen sk x y -> att -> x -> Term Void ty sym Void Void Void Void y 
aAtt alg f x = nf'' alg $ Att f $ up15 $ repr alg x

aSk :: Algebra var ty sym en fk att gen sk x y -> sk -> Term Void ty sym Void Void Void Void y
aSk alg g = nf'' alg $ Sk g

sepBy [] sep = ""
sepBy (x:[]) sep = x
sepBy (x:y ) sep = x ++ sep ++ (sepBy y sep)

sepBy' x y = sepBy y x

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Eq en, Eq fk, Eq att)
  => Show (Algebra var ty sym en fk att gen sk x y) where
  show (Algebra sch en nf repr ty nf' repr' teqs) = 
    "algebra\n" ++ l ++ "\ntype-algeba\n" ++ w ++ sepBy' "\n" (Prelude.map show $ Set.toList $ teqs)
      where w = "nulls\n" ++ sepBy' "\n" (Prelude.map (\ty' -> show ty' ++ " = { " ++ show (Set.toList $ ty ty') ++ " }") (Set.toList $ Typeside.tys $ Schema.typeside sch)) 
            h = Prelude.map (\en' -> show en' ++ "\n-------------\n" ++ (sepBy' "\n" $ Prelude.map (\x -> show x ++ ": " 
                 ++ (sepBy (Prelude.map (f x) $ fksFrom'  sch en') ",") ++ ", " 
                 ++ (sepBy (Prelude.map (g x) $ attsFrom' sch en') ",")) $ Set.toList $ en en')) (Set.toList $ Schema.ens sch)
            l = sepBy' "\n" h
            f x (fk,en') = show   fk  ++ " = " ++ (show $ aFk alg  fk x )
            g x (att,ty) = show   att ++ " = " ++ (show $ aAtt alg att x )
            alg = Algebra sch en nf repr ty nf' repr' teqs
          



fksFrom :: Eq en => Collage var ty sym en fk att gen sk -> en -> [(fk,en)]
fksFrom sch en = f $ Map.assocs $ cfks sch
  where f [] = []
        f ((fk,(en1,t)):l) = if en1 == en then (fk,t) : (f l) else f l


attsFrom :: Eq en => Collage var ty sym en fk att gen sk -> en -> [(att,ty)]
attsFrom sch en = f $ Map.assocs $ catts sch
  where f [] = []
        f ((fk,(en1,t)):l) = if en1 == en then (fk,t) : (f l) else f l


fksFrom' :: Eq en => Schema var ty sym en fk att  -> en -> [(fk,en)]
fksFrom' sch en = f $ Map.assocs $ Schema.fks sch
  where f [] = []
        f ((fk,(en1,t)):l) = if en1 == en then (fk,t) : (f l) else f l


attsFrom' :: Eq en => Schema var ty sym en fk att -> en -> [(att,ty)]
attsFrom' sch en = f $ Map.assocs $ Schema.atts sch
  where f [] = []
        f ((fk,(en1,t)):l) = if en1 == en then (fk,t) : (f l) else f l


data Presentation var ty sym en fk att gen sk
 = Presentation {
    gens    :: Map gen en
  , sks     :: Map sk ty
  , eqs     :: Set (EQ Void ty sym en fk att gen sk)
}


instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk)
  => Show (Presentation var ty sym en fk att gen sk) where
  show (Presentation ens fks eqs) = "presentation {\n" ++
    "generators\n\t" ++ showCtx' ens ++
    "\nequations\n\t" ++ intercalate "\n\t" (Prelude.map show $ Set.toList eqs) ++ "}"

data Instance var ty sym en fk att gen sk x y
  = Instance { 
    schema  :: Schema var ty sym en fk att
  , pres    :: Presentation var ty sym en fk att gen sk
  , dp      :: EQ Void ty sym en fk att gen sk -> Bool
  , algebra :: Algebra var ty sym en fk att gen sk x y
  }

data InstanceEx :: * where
  InstanceEx :: forall var ty sym en fk att gen sk x y. 
   (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, 
    Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Ord x, Ord y,
    Typeable var, Typeable ty, Typeable sym, Typeable en, Typeable fk, Typeable att, Typeable gen, Typeable sk, Typeable x, Typeable y) =>
   Instance var ty sym en fk att gen sk x y -> InstanceEx

deriving instance Show (InstanceEx) 


instToCol :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk)
   => Schema var ty sym en fk att -> Presentation var ty sym en fk att gen sk -> Collage (()+var) ty sym en fk att gen sk
instToCol sch (Presentation gens sks eqs) =
 Collage (Set.union e1 e2) (ctys schcol)
  (cens schcol) (csyms schcol) (cfks schcol) (catts schcol) gens sks
   where schcol = schToCol sch
         e1 = Set.map (\(EQ (l,r)) -> (Map.empty, EQ (up4 l, up4 r))) eqs
         e2 = Set.map (\(g, EQ (l,r))->(g, EQ (up5 l, up5 r))) $ ceqs schcol


up5 :: Term var ty sym en fk att Void Void -> Term var ty sym en fk att gen sk
up5 (Var v) = Var v
up5 (Sym f x) = Sym f $ Prelude.map up5 x
up5 (Fk f a) = Fk f $ up5 a
up5 (Att f a) = Att f $ up5 a
up5 (Gen f) = absurd f
up5 (Sk f) = absurd f

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Eq en,
  Eq fk, Eq att)
  => Show (Instance var ty sym en fk att gen sk x y) where
  show (Instance _ p _ alg) = "instance\n"
    ++ show p ++
    "\n" ++ show alg 

showCtx' m = intercalate "\n\t" $ Prelude.map (\(k,v) -> show k ++ " : " ++ show v) $ Map.toList m 




-- in java we just use pointer equality.  this is better, but really
-- we want that the intances denote the same set-valued functor,
-- possibly up to natural isomorphism. in practice equality only
-- happens during type checking, so the check below suffices... but
-- hopefully it won't incur a performance penalty.  side note:
-- eventually schema equality will need to be relaxed too.
instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Eq x, Eq y)
  => Eq (Instance var ty sym en fk att gen sk x y) where
  (==) (Instance schema (Presentation gens sks eqs) _ _) (Instance schema' (Presentation gens' sks' eqs') _ _)
    = (schema == schema') && (gens == gens') && (sks == sks') && (eqs == eqs')


-- adds one equation per fact in the algebra.
algebraToPresentation :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk, Ord y, Ord x)
  => Algebra var ty sym en fk att gen sk x y
  -> Presentation var ty sym en fk att x y 
algebraToPresentation (alg@(Algebra sch en nf repr ty nf' repr' teqs)) = Presentation gens sks eqs  
 where gens = Map.fromList $ reify en $ Schema.ens sch
       sks = Map.fromList $ reify ty $ Typeside.tys $ Schema.typeside sch 
       eqs1 = concat $ Prelude.map (\(x,en) -> f x en) reified
       eqs2 = concat $ Prelude.map (\(x,en) -> g x en) reified
       eqs = Set.fromList $ eqs1 ++ eqs2
       reified = reify en (Schema.ens sch) 
       f x e = Prelude.map (\(fk,_) -> f' x fk) $ fksFrom' sch e
       g x e = Prelude.map (\(att,_) -> g' x att) $ attsFrom' sch e
       f' x fk = EQ (Fk fk (Gen x), Gen $ aFk alg fk x)
       g' x att = EQ (Att att (Gen x), up6 $ aAtt alg att x)
       
 

up6 :: Term Void ty sym Void Void Void Void sk -> Term var ty sym en fk att gen sk
up6 (Var v) = absurd v
up6 (Gen g) = absurd g
up6 (Sk  s) = Sk s
up6 (Fk  f a) = absurd f
up6 (Att f a) = absurd f
up6 (Sym f as) = Sym f $ Prelude.map up6 as

reify :: (Ord x, Ord en) => (en -> Set x) -> Set en -> [ (x, en) ]
reify f s = concat $ Set.toList $ Set.map (\en-> Set.toList $ Set.map (\x->(x,en)) $ f en) $ s


initialInstance :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk)
 => Presentation var ty sym en fk att gen sk -> (EQ (()+var) ty sym en fk att gen sk -> Bool) 
 -> Schema var ty sym en fk att ->
 Instance var ty sym en fk att gen sk (GTerm en fk gen) (TTerm en fk att gen sk)
initialInstance p dp sch = Instance sch p dp' $ initialAlgebra p dp sch 
 where dp' (EQ (lhs, rhs)) = dp $ EQ (up4 lhs, up4 rhs)
 
up15 :: Term Void Void Void en fk Void gen Void -> Term Void ty sym en fk att gen sk
up15 = up

initialAlgebra :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk)
 => Presentation var ty sym en fk att gen sk -> (EQ (()+var) ty sym en fk att gen sk -> Bool) 
 -> Schema var ty sym en fk att ->
 Algebra var ty sym en fk att gen sk (GTerm en fk gen) (TTerm en fk att gen sk)
initialAlgebra p dp sch = simplify' this
 where this = Algebra sch en nf repr ty nf' repr' teqs
       col = instToCol sch p
       ens  = assembleGens col (close col dp)
       en k = lookup2 k ens
       nf e = let t = typeOf col e 
                  f [] = undefined -- impossible
                  f (a:b) = if dp (EQ (up a, up e)) then a else f b
              in f $ Set.toList $ lookup2 t ens 
       repr x = x
               
       tys = assembleSks col ens    
       ty y = lookup2 y tys    
       nf' (Left g) = Sk $ Left g
       nf' (Right (x, att)) = Sk $ Right (repr x, att) 
       --repr' :: (TTerm en fk att gen sk) -> Term Void ty sym en fk att gen sk    
       repr' (Left g) = Sk g
       repr' (Right (x, att)) = Att att $ up15 $ repr x 
       teqs' = Prelude.concatMap (\(e, EQ (lhs,rhs)) -> Prelude.map (\x -> EQ (nf'' this $ subst' lhs x, nf'' this $ subst' rhs x)) (Set.toList $ en e)) $ Set.toList $ obs_eqs sch
       teqs = Set.union (Set.fromList teqs') (Set.map (\(EQ (lhs,rhs)) -> EQ (nf'' this lhs, nf'' this rhs)) (Set.filter hasTypeType' $ eqs0 p))

eqs0 (Presentation _ _ x) = x

subst' :: Term () ty sym en fk att Void Void -> GTerm en fk gen -> Term Void ty sym en fk att gen sk
subst' (Var ()) t = up t
subst' (Gen f) t = absurd f
subst' (Sk f) t = absurd f
subst' (Sym fs a) t = Sym fs (Prelude.map (\x -> subst' x t) a) 
subst' (Att f a) t = Att f $ subst' a t
subst' (Fk f a) t = Fk f $ subst' a t

hasTypeType :: Term Void ty sym en fk att gen sk -> Bool
hasTypeType (Var f) = absurd f
hasTypeType (Sym f as) = True
hasTypeType (Att f a) = True
hasTypeType (Sk f) = True
hasTypeType (Gen f) = False
hasTypeType (Fk f a) = False

hasTypeType' :: EQ Void ty sym en fk att gen sk -> Bool
hasTypeType' (EQ (lhs, rhs)) = hasTypeType lhs

       
fromListAccum :: (Ord v, Ord k) => [(k, v)] -> Map k (Set v)
fromListAccum [] = Map.empty
fromListAccum ((k,v):tl) = case Map.lookup k r of
   Just s -> Map.insert k (Set.insert v s) r 
   Nothing -> Map.insert k (Set.singleton v) r
  where r = fromListAccum tl

assembleSks :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Show en, Ord en) 
 => Collage var ty sym en fk att gen sk -> Map en (Set (GTerm en fk gen)) ->
 Map ty (Set (TTerm en fk att gen sk))
assembleSks col ens = unionWith Set.union sks $ fromListAccum gens
 where gens = Prelude.concatMap (\(en,set) -> Prelude.concatMap (\term -> Prelude.concatMap (\(att,ty) -> [(ty,(Right) (term,att))]) $ attsFrom col en) $ Set.toList $ set) $ Map.toList $ ens
       sks = Prelude.foldr (\(sk,t) m -> Map.insert t (Set.insert (Left sk) (lookup2 t m)) m) ret $ Map.toList $ csks col
       ret = Map.fromList $ Prelude.map (\x -> (x,Set.empty)) $ Set.toList $ ctys col


type GTerm en fk gen = Term Void Void Void en fk Void gen Void

type TTerm en fk att gen sk = Either sk (GTerm en fk gen, att)


assembleGens :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en) 
 => Collage var ty sym en fk att gen sk -> [ GTerm en fk gen ] -> Map en (Set (GTerm en fk gen))
assembleGens col [] = Map.fromList $ Prelude.map (\x -> (x,Set.empty)) $ Set.toList $ cens col
assembleGens col (e:tl) = Map.insert t (Set.insert e s) m
 where m = assembleGens col tl
       t = typeOf col e
       s = case Map.lookup t m of
            Just s -> s
            Nothing -> undefined --impossible
       
close :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en)
 => Collage var ty sym en fk att gen sk -> (EQ var ty sym en fk att gen sk -> Bool) -> [ (Term Void Void Void en fk Void gen Void) ]
close col dp = y' (close1m dp col) $ Prelude.map Gen $ Map.keys $ cgens col
 where y' f x = y f x
       y f x = let z = f x in if x == z then x else y f z

close1m dp col = dedup dp . concatMap (close1 col dp)

dedup dp = nubBy (\x y -> dp (EQ (up x, up y)))

close1 :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en)
 => Collage var ty sym en fk att gen sk -> (EQ var ty sym en fk att gen sk -> Bool) -> Term Void Void Void en fk Void gen Void -> [ (Term Void Void Void en fk Void gen Void) ]
close1 col dp e = e:(Prelude.map (\(x,_) -> Fk x e) l)
 where t = typeOf col e
       l = fksFrom col t
      -- f [] = 

 
typeOf :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en)
  => Collage var ty sym en fk att gen sk -> Term Void Void Void en fk Void gen Void -> en
typeOf col e = case typeOf' col Map.empty (up e) of
  Left _ -> undefined
  Right x -> case x of
               Left _ -> undefined
               Right y -> y



--------------------------------------------------------------------------------


data InstanceExp where
  InstanceVar :: String -> InstanceExp
  InstanceInitial :: SchemaExp -> InstanceExp

  InstanceDelta :: MappingExp -> InstanceExp -> InstanceExp
  InstanceSigma :: MappingExp -> InstanceExp -> InstanceExp
  InstancePi :: MappingExp -> InstanceExp -> InstanceExp

  InstanceEval :: QueryExp -> InstanceExp -> InstanceExp
  InstanceCoEval :: MappingExp -> InstanceExp -> InstanceExp

  InstanceRaw :: InstExpRaw' -> InstanceExp
  deriving (Eq,Show)

data InstExpRaw' = InstExpRaw' {
    instraw_schema :: SchemaExp
  , instraw_gens  :: [(String, String)]
--  , instraw_sks :: [(String, String)]
  , instraw_oeqs  :: [(RawTerm, RawTerm)]
  , instraw_options :: [(String, String)]
} deriving (Eq,Show)

type Gen = String
type Sk = String

conv' :: (Typeable ty,Show ty) => [(String, String)] -> Err [(String, ty)]
conv' [] = pure []
conv' ((att,ty):tl) = case cast ty of 
   Just ty' -> do x <- conv' tl
                  return $ (att, ty'):x
   Nothing -> Left $ "Not in schema/typeside: " ++ show ty   


split' [] = ([],[])
split' ((w, Left x):tl) = let (a,b) = split' tl 
                       in  ((w,x):a, b) 
split' ((w, Right x):tl) = let (a,b) = split' tl 
                        in  (a, (w,x):b) 

evalInstanceRaw' :: forall var ty sym en fk att. (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Typeable sym, Typeable ty, Ord en, Typeable fk, Typeable att, Ord fk, Typeable en, Show fk, Ord att, Show att, Show fk, Show en) 
 => Schema var ty sym en fk att -> InstExpRaw' -> Err (Presentation var ty sym en fk att Gen Sk)
evalInstanceRaw' sch (InstExpRaw' _ gens0 eqs ops) = 
  do (gens, sks) <- zzz
     gens' <- toMapSafely gens 
     gens'' <- conv' $ Map.toList gens'
     sks' <- toMapSafely sks 
     sks'' <- conv' $ Map.toList sks'
     eqs' <- f gens sks eqs 
     typecheckPresentation sch $ Presentation (Map.fromList gens'') (Map.fromList sks'') eqs'
 where     
  zzz = do y <- mapM w gens0
           return $ split' y
  w (a, b) = case cast b of
               Nothing -> case cast b of 
                 Nothing -> Left $ "Not a gen or sch, " ++ b 
                 Just b' -> return (a, Right b')
               Just b' -> return (a, Left b')  
  keys = fst . unzip 
  --f :: [(String, String, RawTerm, RawTerm)] -> Err (Set (En, EQ () ty   sym  en fk att  Void Void))
  f gens sks [] = pure $ Set.empty
  f gens sks ((lhs, rhs):eqs') = do lhs' <- g (keys gens) (keys sks) lhs
                                    rhs' <- g (keys gens) (keys sks) rhs
                                    rest <- f gens sks eqs'
                                    pure $ Set.insert (EQ (lhs', rhs')) rest
 --g' :: [String] -> RawTerm -> Err (Term Void Void Void en fk Void Gen Void)                               
  g' gens (RawApp x []) | elem x gens = pure $ Gen x
  g' gens (RawApp x (a:[])) | elem' x (keys $ Map.toList $ sch_fks sch) = do a' <- g' gens a
                                                                             case cast x :: Maybe fk of
                                                                               Just x' -> return $ Fk x' a' 
  g' gens x = Left $ "cannot type " ++ (show x)                                                                        

  g :: [String] -> [String] -> RawTerm -> Err (Term Void ty sym en fk att Gen Sk)                                   
  g gens sks (RawApp x []) | elem x gens = pure $ Gen x
  g gens sks (RawApp x []) | elem x sks = pure $ Sk x
  
  g gens sks (RawApp x (a:[])) | elem' x (keys $ Map.toList $ sch_fks sch) = do a' <- g' gens a
                                                                                case cast x of
                                                                                 Just x' -> return $ Fk x' a' 
  g gens sks (RawApp x (a:[])) | elem' x (keys $ Map.toList $ sch_atts sch) = do a' <- g' gens a
                                                                                 case cast x of
                                                                                  Just x' -> return $ Att x' a' 
  g gens sks (RawApp v l) = do l' <- mapM (g gens sks) l
                               case cast v :: Maybe sym of
                                  Just x -> pure $ Sym x l'
                                  Nothing -> Left $ "Cannot type: " ++ v   


                                        
--todo: check model satisfaction for algebra here
evalInstanceRaw :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Typeable sym, Typeable ty, Ord en, Typeable fk, Typeable att, Ord fk, Typeable en, Show fk, Ord att, Show att, Show fk, Show en, Typeable var) 
  => Schema var ty sym en fk att -> InstExpRaw' -> Err InstanceEx
evalInstanceRaw ty t =
 do r <- evalInstanceRaw' ty t 
    l <- toOptions $ instraw_options t
    p <- createProver (instToCol ty r) l
    pure $ InstanceEx $ initialInstance r (f p) ty 
 where
  f p (EQ (l,r)) = prove p (Map.fromList []) (EQ ( l,  r))
  

----------------------------------------------------------------------------------

evalSigmaInst
  :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y, Eq en', Eq fk', Eq att')
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en fk att gen sk x y
  -> Instance var ty sym en' fk' att' gen sk (GTerm en fk gen) (TTerm en fk att gen sk)
evalSigmaInst = undefined 

evalDeltaAlgebra
  :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y, Eq en', Eq fk', Eq att')
  => Mapping  var ty sym en  fk  att  en'       fk' att'
  -> Instance var ty sym en' fk' att' gen       sk  x       y
  -> Algebra  var ty sym en  fk  att  (en',gen) sk  (en',x) y
evalDeltaAlgebra = undefined --todo

evalDeltaInst
  :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y, Eq en', Eq fk', Eq att')
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en' fk' att' gen sk x y
  -> Instance var ty sym en fk att (en',gen) sk (en',x) y
evalDeltaInst = undefined --todo

-- TODO all of these need to be changed at once
--data ErrEval = ErrSchemaMismatch | ErrQueryEvalTodo | ErrMappingEvalTodo | ErrInstanceEvalTodo


