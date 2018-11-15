{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DuplicateRecordFields  #-}
{-# LANGUAGE ExplicitForAll         #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE ImpredicativeTypes     #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LiberalTypeSynonyms    #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE IncoherentInstances    #-}

module Language.Term where

import           Data.Map.Strict as Map hiding (foldr, size)
import           Data.Maybe
import           Data.Set        as Set hiding (foldr, size)
import           Data.Void
import           Language.Common
import           Prelude         hiding (EQ)
import           Control.DeepSeq



class Deps a where
  deps :: a -> [(String, Kind)]

occurs :: (Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk)
 => Head ty sym en fk att gen sk -> Term var ty sym en fk att gen sk -> Bool
occurs _ (Var _)     = False
occurs h (Sk h')     = h == HSk h'
occurs h (Gen h')    = h == HGen h'
occurs h (Fk h' a)   = h == HFk h' || occurs h a
occurs h (Att h' a)  = h == HAtt h' || occurs h a
occurs h (Sym h' as) = h == HSym h' || or (Prelude.map (occurs h) as)


find :: (Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk)
 => Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk) -> Maybe (Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)
find = f . Set.toList
 where g (Var _) _ = Nothing
       g (Sk y) t = if occurs (HSk y) t then Nothing else Just (HSk y, t)
       g (Gen y) t = if occurs (HGen y) t then Nothing else Just (HGen y, t)
       g (Sym _ []) _ = Nothing --if occurs (HSym y) t then Nothing else Just (HSym y, t)
       --g (Sym f' (a:b)) t = --Nothing --case g a t of
                            -- Nothing -> g (Sym f' b) t
                             --Just y -> Just y
       g _ _ = Nothing
       f [] = Nothing
       f ((m, _):_) | not (Map.null m) = Nothing
       f ((_, EQ (lhs, rhs)):tl) = case g lhs rhs of
          Nothing -> case g rhs lhs of
            Nothing     -> f tl
            Just (y, r) -> Just (y, r)
          Just (y, r) -> Just (y, r)


replace' :: (Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk)
 => Head ty sym en fk att gen sk -> Term var ty sym en fk att gen sk -> Term var ty sym en fk att gen sk -> Term var ty sym en fk att gen sk
replace' toReplace replacer (Sk s) = if (HSk s == toReplace) then replacer else Sk s
replace' toReplace replacer (Gen s) = if (HGen s == toReplace) then replacer else Gen s
replace' toReplace replacer (Sym f []) = if (HSym f == toReplace) then replacer else Sym f []
replace' toReplace replacer (Sym f a) = Sym f $ Prelude.map (replace' toReplace replacer) a
replace' toReplace replacer (Fk f a) = Fk f $ replace' toReplace replacer a
replace' toReplace replacer (Att f a) = Att f $ replace' toReplace replacer a
replace' _ _ (Var v) = Var v

replaceRepeatedly :: (Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk) =>
 [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)] ->
 Term var ty sym en fk att gen sk -> Term var ty sym en fk att gen sk
replaceRepeatedly [] t        = t
replaceRepeatedly ((s,t):r) e = replaceRepeatedly r $ replace' s t e


simplifyCol
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> (Collage var ty sym en fk att gen sk, [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)])
simplifyCol (Collage ceqs' ctys' cens' csyms' cfks' catts' cgens' csks')
  = (Collage ceqs'' ctys' cens' csyms' cfks' catts' cgens'' csks'', f)
 where (ceqs'', f) = simplify'' ceqs' []
       cgens'' = Map.fromList $ Prelude.filter (\(x,_) -> not $ Prelude.elem (HGen x) $ fst $ unzip f) $ Map.toList cgens'
       csks''  = Map.fromList $ Prelude.filter (\(x,_) -> not $ Prelude.elem (HSk  x) $ fst $ unzip f) $ Map.toList csks'



simplify''
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Set (Ctx var (ty + en), EQ var ty sym en fk att gen sk)
  -> [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)]
  -> (Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk), [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)])
simplify'' eqs subst' = case simplify eqs of
  Nothing             -> (eqs, subst')
  Just (eqs1, subst1) -> simplify'' eqs1 $ subst' ++ [subst1]


simplify
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk)
  -> Maybe (Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk), (Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk))
simplify eqs = case find eqs of
 Nothing -> Nothing
 Just (toRemove, replacer) -> let eqs2 = Set.map (\(ctx, EQ (lhs, rhs)) -> (ctx, EQ (replace' toRemove replacer lhs, replace' toRemove replacer rhs))) eqs
                                  eqs3 = Set.filter (\(_,EQ (x,y)) -> not (x == y)) eqs2
                 in Just $ (eqs3,(toRemove, replacer))

class Up x y where
  upgr :: x -> y

upp :: (Up var var', Up ty ty', Up sym sym', Up en en', Up fk fk', Up att att', Up gen gen', Up sk sk')
  => Term var ty sym en fk att gen sk -> Term var' ty' sym' en' fk' att' gen' sk'
upp (Var v  ) = Var $ upgr v
upp (Sym f a) = Sym (upgr f) $ fmap upp a
upp (Fk  f a) = Fk  (upgr f) $      upp a
upp (Att f a) = Att (upgr f) $      upp a
upp (Gen g  ) = Gen $ upgr g
upp (Sk  s  ) = Sk  $ upgr s

instance Up x x where
  upgr x = x

instance Up Void x where
  upgr = absurd

instance Up x (x + y) where
  upgr = Left

instance Up y (x + y) where
  upgr = Right

data Term var ty sym en fk att gen sk
  -- | Variable.
  = Var var

  -- | Type side function/constant symbol.
  | Sym sym  [Term var ty sym en fk att gen sk]

  -- | Foreign key.
  | Fk  fk   (Term var ty sym en fk att gen sk)

  -- | Attribute.
  | Att att  (Term var ty sym en fk att gen sk)

  -- | Generator.
  | Gen gen

  -- | Skolem term or labelled null; like a generator for a type rather than an entity.
  | Sk  sk

instance (NFData var, NFData ty, NFData sym, NFData en, NFData fk, NFData att, NFData gen, NFData sk) =>
  NFData (Term var ty sym en fk att gen sk) where
    rnf x = case x of
      Var v   -> rnf v
      Sym f a -> let _ = rnf f in rnf a
      Fk  f a -> let _ = rnf f in rnf a
      Att f a -> let _ = rnf f in rnf a
      Gen   a -> rnf a
      Sk    a -> rnf a

instance (NFData var, NFData ty, NFData sym, NFData en, NFData fk, NFData att, NFData gen, NFData sk) =>
  NFData (EQ var ty sym en fk att gen sk) where
    rnf (EQ (x, y)) = deepseq x $ rnf y

data Head ty sym en fk att gen sk =
   HSym sym
 | HFk fk
 | HAtt att
 | HGen gen
 | HSk sk
  deriving (Eq, Show, Ord)

mapTerm
  :: (var -> var')
  -> (ty  -> ty' )
  -> (sym -> sym')
  -> (en  -> en' )
  -> (fk  -> fk' )
  -> (att -> att')
  -> (gen -> gen')
  -> (sk  -> sk' )
  -> Term var ty sym en fk att gen sk
  -> Term var' ty' sym' en' fk' att' gen' sk'
mapTerm v t r e f a g s x = case x of
  Var w   -> Var $ v w
  Gen w   -> Gen $ g w
  Sk  w   -> Sk  $ s w
  Fk  w u -> Fk  (f w) $ mt u
  Att w u -> Att (a w) $ mt u
  Sym w u -> Sym (r w) $ fmap mt u
  where mt = mapTerm v t r e f a g s

mapVar :: var -> Term () ty sym en fk att gen sk -> Term var ty sym en fk att gen sk
mapVar v t = mapTerm (\_ -> v) id id id id id id id t


size :: Term var ty sym en fk att gen sk -> Integer
size (Var _)    = 1
size (Gen _)    = 1
size (Sk _)     = 1
size (Att _ a)  = 1 + size a
size (Fk _ a)   = 1 + size a
size (Sym _ as) = 1 + (foldr (\x y -> (size x) + y) 0 as)


vars :: Term var ty sym en fk att gen sk -> [var]
vars (Var v)    = [v]
vars (Gen _)    = []
vars (Sk _)     = []
vars (Att _ a)  = vars a
vars (Fk _ a)   = vars a
vars (Sym _ as) = concatMap vars as


instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) =>
  Show (Term var ty sym en fk att gen sk)
  where
    show x = case x of
     Var v      -> show v
     Gen g      -> show g
     Sk  s      -> show s
     Fk  fk  a  -> show a ++ "." ++ show fk
     Att att a  -> show a ++ "." ++ show att
     Sym sym [] -> show sym
     Sym sym az -> show sym ++ "(" ++ (intercalate "," . fmap show $ az) ++ ")"

deriving instance (Eq var, Eq sym, Eq fk, Eq att, Eq gen, Eq sk) => Eq (Term var ty sym en fk att gen sk)

deriving instance (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk) => Ord (Term var ty sym en fk att gen sk)

-- TODO wrap Map class to throw an error (or do something less ad hoc) if a key is ever put twice
type Ctx k v = Map k v

-- Our own pair type for pretty printing purposes
newtype EQ var ty sym en fk att gen sk
  = EQ (Term var ty sym en fk att gen sk, Term var ty sym en fk att gen sk) deriving (Ord,Eq)

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) => Show (EQ var ty sym en fk att gen sk) where
  show (EQ (lhs,rhs)) = show lhs ++ " = " ++ show rhs

data Collage var ty sym en fk att gen sk
  = Collage
  { ceqs  :: Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk)
  , ctys  :: Set ty
  , cens  :: Set en
  , csyms :: Map sym ([ty],ty)
  , cfks  :: Map fk (en, en)
  , catts :: Map att (en, ty)
  , cgens :: Map gen en
  , csks  :: Map sk ty
  } deriving (Eq, Show)

data Morphism var ty sym en fk att gen sk en' fk' att' gen' sk'
  = Morphism {
    m_src  :: Collage (()+var) ty sym en fk att gen sk
  , m_dst  :: Collage (()+var) ty sym en' fk' att' gen' sk'
  , m_ens  :: Map en  en'
  , m_fks  :: Map fk  (Term () Void Void en' fk' Void Void Void)
  , m_atts :: Map att (Term () ty   sym  en' fk' att' Void Void)
  , m_gens :: Map gen (Term Void Void Void en' fk' Void gen' Void)
  , m_sks  :: Map sk  (Term Void  ty   sym  en' fk' att'  gen' sk')
}


trans'
  :: forall var var' ty sym en fk att gen sk en' fk' att' gen' sk'
  .  (Ord gen, Ord sk, Ord fk, Eq var, Ord att, Ord var')
  => Morphism var ty sym en fk att gen sk en' fk' att' gen' sk'
  -> Term var' Void Void en  fk  Void gen  Void
  -> Term var' Void Void en' fk' Void gen' Void
trans' _ (Var x) = Var x
trans' mor (Fk f a) = let x = trans' mor a :: Term var' Void Void en' fk' Void gen' Void
                          y = fromJust $ Map.lookup f $ m_fks mor :: Term () Void Void en' fk' Void Void Void
                     in subst (upp y) x
trans' _ (Sym _ _) = undefined
trans' _ (Att _ _) = undefined
trans' mor (Gen g) = upp $ fromJust $ Map.lookup g (m_gens mor)
trans' _ (Sk _) = undefined

trans :: forall var var' ty sym en fk att gen sk en' fk' att' gen' sk' .
 (Ord gen, Ord sk, Ord fk, Eq var, Ord att, Ord var') =>
 Morphism var ty sym en fk att gen sk en' fk' att' gen' sk' ->
 Term var' ty sym en fk att gen sk -> Term var' ty sym en' fk' att' gen' sk'
trans _ (Var x) = Var x
trans mor (Sym f xs) = Sym f $ Prelude.map (trans mor) xs
trans mor (Gen g) = upp $ fromJust $ Map.lookup g (m_gens mor)
trans mor (Sk s) = upp $ fromJust $ Map.lookup s (m_sks mor)
trans mor (Fk f a) = let x = trans mor a :: Term var' ty sym en' fk' att' gen' sk'
                         y = fromJust $ Map.lookup f $ m_fks mor :: Term () Void Void en' fk' Void Void Void
                     in subst (upp y) x
trans mor (Att f a) = subst (upp $ fromJust $ Map.lookup f (m_atts mor)) $ trans mor a


subst
  :: Eq var
  => Term ()  ty sym en fk att gen sk
  -> Term var ty sym en fk att gen sk
  -> Term var ty sym en fk att gen sk
subst (Var ()  ) t = t
subst (Sym f as) t = Sym f $ (\a -> subst a t) <$> as
subst (Fk  f a ) t = Fk  f $ subst a t
subst (Att f a ) t = Att f $ subst a t
subst (Gen g   ) _ = Gen g
subst (Sk  g   ) _ = Sk  g


checkDoms'
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk, en', fk', att', gen', sk'])
  => Morphism var ty sym en fk att gen sk en' fk' att' gen' sk'
  -> Err ()
checkDoms' mor = do _ <- mapM e $ Set.toList $ cens $ m_src mor
                    _ <- mapM f $ Map.keys $ cfks $ m_src mor
                    _ <- mapM a $ Map.keys $ catts $ m_src mor
                    _ <- mapM g $ Map.keys $ cgens $ m_src mor
                    _ <- mapM s $ Map.keys $ csks $ m_src mor
                    pure ()
  where e en = if Map.member en $ m_ens  mor then pure () else Left $ "No entity mapping for " ++ show en
        f fk = if Map.member fk $ m_fks  mor then pure () else Left $ "No fk mapping for " ++ show fk
        a at = if Map.member at $ m_atts mor then pure () else Left $ "No att mapping for " ++ show at
        g gn = if Map.member gn $ m_gens mor then pure () else Left $ "No gen mapping for " ++ show gn
        s sk = if Map.member sk $ m_sks  mor then pure () else Left $ "No sk mapping for " ++ show sk

typeOfMor
  :: forall var ty sym en fk att gen sk en' fk' att' gen' sk' . (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk, en', fk', att', gen', sk'])
  => Morphism var ty sym en fk att gen sk en' fk' att' gen' sk'
  -> Err ()
typeOfMor mor  = do checkDoms' mor
                    _ <- mapM typeOfMorEns $ Map.toList $ m_ens mor
                    _ <- mapM typeOfMorFks $ Map.toList $ m_fks mor
                    _ <- mapM typeOfMorAtts $ Map.toList $ m_atts mor
                    _ <- mapM typeOfMorGens $ Map.toList $ m_gens mor
                    _ <- mapM typeOfMorSks $ Map.toList $ m_sks mor
                    pure ()
 where transE en = case (Map.lookup en (m_ens mor)) of
                    Just x  -> x
                    Nothing -> undefined
       typeOfMorEns (e,e') | elem e (cens $ m_src mor) && elem e' (cens $ m_dst mor) = pure ()
       typeOfMorEns (e,e') = Left $ "Bad entity mapping " ++ show e ++ " -> " ++ show e'
       typeOfMorFks :: (fk, Term () Void Void en' fk' Void Void Void) -> Err ()
       typeOfMorFks (fk,e) | Map.member fk (cfks $ m_src mor)
         = let (s,t) = fromJust $ Map.lookup fk $ cfks $ m_src mor
               (s',t') = (transE s, transE t)
           in do t0 <- typeOf' (m_dst mor) (Map.fromList [(Left (), Right s')]) $ upp e
                 if t0 == Right t' then pure () else Left $ "1Ill typed in " ++ show fk ++ ": " ++ show e
       typeOfMorFks (e,e') = Left $ "Bad fk mapping " ++ show e ++ " -> " ++ show e'
       typeOfMorAtts (att,e) | Map.member att (catts $ m_src mor)
         = let (s,t) = fromJust $ Map.lookup att $ catts $ m_src mor
               s' = transE s
           in do t0 <- typeOf' (m_dst mor) (Map.fromList [(Left (),Right s')]) $ upp e
                 if t0 == Left t then pure () else Left $ "2Ill typed attribute, " ++ show att ++ " expression " ++ show e
                  ++ ", computed type " ++ show t0 ++ " and required type " ++ show t
       typeOfMorAtts (e,e') = Left $ "Bad att mapping " ++ show e ++ " -> " ++ show e'
       typeOfMorGens (gen,e) | Map.member gen (cgens $ m_src mor)
         = let t = fromJust $ Map.lookup gen $ cgens $ m_src mor
               t' = transE t
           in do t0 <- typeOf' (m_dst mor) (Map.fromList []) $ upp e
                 if t0 == Right t' then pure () else Left $ "3Ill typed in " ++ show gen ++ ": " ++ show e
       typeOfMorGens (e,e') = Left $ "Bad gen mapping " ++ show e ++ " -> " ++ show e'
       typeOfMorSks (sk,e) | Map.member sk (csks $ m_src mor)
         = let t = fromJust $ Map.lookup sk $ csks $ m_src mor
           in do t0 <- typeOf' (m_dst mor) (Map.fromList []) $ upp e
                 if t0 == Left t then pure () else Left $ "4Ill typed in " ++ show sk ++ ": " ++ show e
       typeOfMorSks (e,e') = Left $ "Bad null mapping " ++ show e ++ " -> " ++ show e'





initGround :: (Ord ty, Ord en) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool)
initGround col = (me', mt')
 where me = Map.fromList $ Prelude.map (\en -> (en, False)) $ Set.toList $ cens col
       mt = Map.fromList $ Prelude.map (\ty -> (ty, False)) $ Set.toList $ ctys col
       me' = Prelude.foldr (\(_, en) m -> Map.insert en True m) me $ Map.toList $ cgens col
       mt' = Prelude.foldr (\(_, ty) m -> Map.insert ty True m) mt $ Map.toList $ csks col


closeGround :: (Ord ty, Ord en) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool) -> (Map en Bool, Map ty Bool)
closeGround col (me, mt) = (me', mt'')
 where mt''= Prelude.foldr (\(_, (tys,ty)) m -> if and ((flip lookup2 mt') <$> tys) then Map.insert ty True m else m) mt' $ Map.toList $ csyms col
       mt' = Prelude.foldr (\(_, (en, ty)) m -> if lookup2 en me' then Map.insert ty True m else m)                   mt  $ Map.toList $ catts col
       me' = Prelude.foldr (\(_, (en, _))  m -> if lookup2 en me  then Map.insert en True m else m)                   me  $ Map.toList $ cfks  col

iterGround :: (ShowOrdN '[ty, en]) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool) -> (Map en Bool, Map ty Bool)
iterGround col r = if r == r' then r else iterGround col r'
 where r' = closeGround col r

computeGround :: (ShowOrdN '[ty, en]) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool)
computeGround col = iterGround col $ initGround col

allSortsInhabited :: (ShowOrdN '[ty, en]) => Collage var ty sym en fk att gen sk -> Bool
allSortsInhabited col = t && f
 where (me, mt) = computeGround col
       t = and $ Map.elems me
       f = and $ Map.elems mt


-- I've given up on non string based error handling for now
typeOf'
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Ctx var (ty + en)
  -> Term    var ty sym en fk att gen sk
  -> Err (ty + en)
typeOf' _ ctx (Var v) = note ("Unbound variable: " ++ show v) $ Map.lookup v ctx
typeOf' col _ (Gen g) = case Map.lookup g $ cgens col of
  Nothing -> Left $ "Unknown generator: " ++ show g
  Just t  -> Right $ Right t
typeOf' col _ (Sk s) = case Map.lookup s $ csks col of
  Nothing -> Left $ "Unknown labelled null: " ++ show s
  Just t  -> Right $ Left t
typeOf' col ctx (xx@(Fk f a)) = case Map.lookup f $ cfks col of
  Nothing     -> Left $ "Unknown foreign key: " ++ show f
  Just (s, t) -> do s' <- typeOf' col ctx a
                    if (Right s) == s' then pure $ Right t else Left $ "Expected argument to have entity " ++
                     show s ++ " but given " ++ show s' ++ " in " ++ (show xx)
typeOf' col ctx (xx@(Att f a)) = case Map.lookup f $ catts col of
  Nothing -> Left $ "Unknown attribute: " ++ show f
  Just (s, t) -> do s' <- typeOf' col ctx a
                    if (Right s) == s' then pure $ Left t else Left $ "Expected argument to have entity " ++
                     show s ++ " but given " ++ show s' ++ " in " ++ (show xx)
typeOf' col ctx (xx@(Sym f a)) = case Map.lookup f $ csyms col of
  Nothing -> Left $ "Unknown function symbol: " ++ show f
  Just (s, t) -> do s' <- mapM (typeOf' col ctx) a
                    if length s' == length s
                    then if (Left <$> s) == s'
                         then pure $ Left t
                         else Left $ "Expected arguments to have types " ++
                     show s ++ " but given " ++ show s' ++ " in " ++ (show $ xx)
                    else Left $ "Expected argument to have arity " ++
                     show (length s) ++ " but given " ++ show (length s') ++ " in " ++ (show $ xx)

typeOfEq'
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> (Ctx var (ty + en), EQ var ty sym en fk att gen sk)
  -> Err (ty + en)
typeOfEq' col (ctx, EQ (lhs, rhs)) = do
  lhs' <- typeOf' col ctx lhs
  rhs' <- typeOf' col ctx rhs
  if lhs' == rhs'
  then Right $ lhs'
  else Left  $ "Equation lhs has type " ++ show lhs' ++ " but rhs has type " ++ show rhs'

checkDoms :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Err ()
checkDoms col = do
  _ <- mapM f    $ Map.elems $ csyms col
  _ <- mapM g    $ Map.elems $ cfks  col
  _ <- mapM h    $ Map.elems $ catts col
  _ <- mapM isEn $ Map.elems $ cgens col
  _ <- mapM isTy $ Map.elems $ csks  col
  pure ()
 where f (t1,t2) = do _ <- mapM isTy t1
                      isTy t2
       g (e1,e2) = do isEn e1
                      isEn e2
       h (e,t) = do isEn e
                    isTy t
       isEn x = if Set.member x $ cens col
                then pure ()
                else Left $ "Not an entity: " ++ show x
       isTy x = if Set.member x $ ctys col
                then pure ()
                else Left $ "Not a type: " ++ show x


typeOfCol
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Err ()
typeOfCol col = do
  checkDoms col
  mapM_ (typeOfEq' col) $ Set.toList $ ceqs col
  pure ()

data RawTerm = RawApp String [RawTerm]
 deriving Eq

instance Show RawTerm where
 show (RawApp sym az) = show sym ++ "(" ++ (intercalate "," . fmap show $ az) ++ ")"


--Set is not Traversable! Lame
