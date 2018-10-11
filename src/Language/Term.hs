{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Term where

import Prelude hiding (EQ)
import Data.Set as Set hiding (size, foldr)
import Data.Map.Strict as Map hiding (size, foldr)
import Data.Void
import Data.List (intercalate)
import Language.Common
import Data.Maybe


occurs :: (Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk) 
 => Head ty sym en fk att gen sk -> Term var ty sym en fk att gen sk -> Bool
occurs h (Var v) = False 
occurs h (Sk h') = h == HSk h' 
occurs h (Gen h') = h == HGen h'
occurs h (Fk h' a) = h == HFk h' || occurs h a 
occurs h (Att h' a) = h == HAtt h' || occurs h a 
occurs h (Sym h' as) = h == HSym h' || or (Prelude.map (occurs h) as)


find :: (Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk) 
 => Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk) -> Maybe (Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)
find = f . Set.toList
 where g (Var _) _ = Nothing
       g (Sk y) t = if occurs (HSk y) t then Nothing else Just (HSk y, t)
       g (Gen y) t = if occurs (HGen y) t then Nothing else Just (HGen y, t) 
       g (Sym y []) t = Nothing --if occurs (HSym y) t then Nothing else Just (HSym y, t)
       --g (Sym f' (a:b)) t = --Nothing --case g a t of
                            -- Nothing -> g (Sym f' b) t
                             --Just y -> Just y
       g _ _ = Nothing
       f [] = Nothing
       f ((m, _):tl) | not (Map.null m) = Nothing
       f ((_, EQ (lhs, rhs)):tl) = case g lhs rhs of
          Nothing -> case g rhs lhs of
            Nothing -> f tl
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
replace' _ _ _ = undefined

replaceRepeatedly :: (Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk) =>
 [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)] ->
 Term var ty sym en fk att gen sk -> Term var ty sym en fk att gen sk
replaceRepeatedly [] t = t
replaceRepeatedly ((s,t):r) e = replaceRepeatedly r $ replace' s t e


simplifyCol :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk) =>
 Collage var ty sym en fk att gen sk
  -> (Collage var ty sym en fk att gen sk,
    [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)])
simplifyCol (col@(Collage ceqs ctys cens csyms cfks catts cgens csks)) 
  = (Collage ceqs' ctys cens csyms cfks catts cgens' csks', f)
 where (ceqs', f) = simplify'' ceqs []
       cgens' = Map.fromList $ Prelude.filter (\(x,_) -> not $ Prelude.elem (HGen x) $ fst $ unzip f) $ Map.toList cgens
       csks'  = Map.fromList $ Prelude.filter (\(x,_) -> not $ Prelude.elem (HSk x) $ fst $ unzip f) $ Map.toList csks



simplify'' :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk) =>
 Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk) ->
 [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)] 
 -> (Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk),
    [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)])
simplify'' eqs subst = case simplify eqs of
  Nothing -> (eqs, subst)
  Just (eqs1, subst1) -> simplify'' eqs1 $ subst ++ [subst1] 


simplify :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk) =>
 Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk) ->
 Maybe (Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk),
    (Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk))
simplify eqs = case find eqs of
 Nothing -> Nothing
 Just (toRemove, replacer) -> let eqs2 = Set.map (\(ctx, EQ (lhs, rhs)) -> (ctx, EQ (replace' toRemove replacer lhs, replace' toRemove replacer rhs))) eqs
                                  eqs3 = Set.filter (\(_,EQ (x,y)) -> not (x == y)) eqs2
                 in Just $ (eqs3,(toRemove, replacer))
 



data Term var ty sym en fk att gen sk
  = Var var
  | Sym sym  [Term var ty sym en fk att gen sk]
  | Fk  fk   (Term var ty sym en fk att gen sk)
  | Att att  (Term var ty sym en fk att gen sk)
  | Gen gen
  | Sk  sk

data Head ty sym en fk att gen sk =
   HSym sym
 | HFk fk
 | HAtt att
 | HGen gen
 | HSk sk
  deriving (Eq, Show, Ord)

size :: Term var ty sym en fk att gen sk -> Integer
size (Var _) = 1
size (Gen _) = 1
size (Sk _) = 1
size (Att _ a) = 1 + size a
size (Fk _ a) = 1 + size a
size (Sym _ as) = 1 + (foldr (\x y -> (size x) + y) 0 as)


vars :: Term var ty sym en fk att gen sk -> [var]
vars (Var v) = [v]
vars (Gen _) = []
vars (Sk _) = []
vars (Att _ a) = vars a
vars (Fk _ a) = vars a
vars (Sym _ as) = concatMap vars as


up :: Term Void Void Void en fk Void gen Void -> Term var ty sym en fk att gen sk
up (Var f) = absurd f
up (Sym f _) = absurd f
up (Fk f a) = Fk f $ up a
up (Att f _) = absurd f
up (Gen f) = Gen f
up (Sk f) = absurd f

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



up4 :: Term Void ty sym en fk att gen sk -> Term x ty sym en fk att gen sk
up4 (Var v) = absurd v
up4 (Sym f x) = Sym f $ Prelude.map up4 x
up4 (Fk f a) = Fk f $ up4 a
up4 (Att f a) = Att f $ up4 a
up4 (Gen f) = Gen f
up4 (Sk f) = Sk f

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

up12 :: Term Void Void Void en fk Void gen Void -> Term var ty sym en fk att gen sk
up12 (Gen g) = Gen g
up12 (Sk sk) = absurd sk
up12 (Var v) = absurd v
up12 (Fk f a) = Fk f $ up12 a
up12 (Att f _) = absurd f
up12 (Sym f _) = absurd f


up13 :: Term () Void Void en' fk' Void Void Void -> Term () ty sym en' fk' att' gen' sk'
up13 (Gen g) = absurd g
up13 (Sk sk) = absurd sk
up13 (Var v) = Var v
up13 (Fk f a) = Fk f $ up13 a
up13 (Att f _) = absurd f
up13 (Sym f _) = absurd f


up14 :: Term () ty   sym  en' fk' att' Void Void -> Term () ty sym en' fk' att' gen' sk'
up14 (Gen g) = absurd g
up14 (Sk sk) = absurd sk
up14 (Var v) = Var v
up14 (Fk f a) = Fk f $ up14 a
up14 (Att f a) = Att f $ up14 a
up14 (Sym f as) = Sym f $ Prelude.map up14 as



trans :: forall var var' ty sym en fk att gen sk en' fk' att' gen' sk' .
 (Ord gen, Ord sk, Ord fk, Eq var, Ord att, Ord var') =>
 Morphism var ty sym en fk att gen sk en' fk' att' gen' sk' ->
 Term var' ty sym en fk att gen sk -> Term var' ty sym en' fk' att' gen' sk'
trans _ (Var x) = Var x
trans mor (Sym f xs) = Sym f $ Prelude.map (trans mor) xs
trans mor (Gen g) = up12 $ fromJust $ Map.lookup g (m_gens mor)
trans mor (Sk s) = up4 $ fromJust $ Map.lookup s (m_sks mor)
trans mor (Fk f a) = let x = trans mor a :: Term var' ty sym en' fk' att' gen' sk'
                         y = fromJust $ Map.lookup f $ m_fks mor :: Term () Void Void en' fk' Void Void Void
                     in subst (up13 y) x
trans mor (Att f a) = subst (up14 $ fromJust $ Map.lookup f (m_atts mor)) $ trans mor a


subst :: Eq var => Term () ty sym en fk att gen sk ->
  Term var ty sym en fk att gen sk -> Term var ty sym en fk att gen sk
subst (Var ()) t = t
subst (Sym f as) t = Sym f $ Prelude.map (\x -> subst x t) as
subst (Fk f a) t = Fk f $ subst a t
subst (Att f a) t = Att f $ subst a t
subst (Gen g) _ = Gen g
subst (Sk g) _ = Sk g


checkDoms' :: forall var ty sym en fk att gen sk en' fk' att' gen' sk' .
   (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym,
    Ord gen', Show gen', Ord sk', Show sk', Ord fk', Show fk', Ord en', Show en', Show att', Ord att')
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
  :: forall var ty sym en fk att gen sk en' fk' att' gen' sk' .
   (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym,
    Ord gen', Show gen', Ord sk', Show sk', Ord fk', Show fk', Ord en', Show en', Show att', Ord att')
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
                    Just x -> x
                    Nothing -> undefined
       typeOfMorEns (e,e') | elem e (cens $ m_src mor) && elem e' (cens $ m_dst mor) = pure ()
       typeOfMorEns (e,e') = Left $ "Bad entity mapping " ++ show e ++ " -> " ++ show e'
       typeOfMorFks :: (fk, Term () Void Void en' fk' Void Void Void) -> Err ()
       typeOfMorFks (fk,e) | Map.member fk (cfks $ m_src mor)
         = let (s,t) = fromJust $ Map.lookup fk $ cfks $ m_src mor
               (s',t') = (transE s, transE t)
           in do t0 <- typeOf' (m_dst mor) (Map.fromList [(Left (), Right s')]) $ up3 e
                 if t0 == Right t' then pure () else Left $ "1Ill typed in " ++ show fk ++ ": " ++ show e
       typeOfMorFks (e,e') = Left $ "Bad fk mapping " ++ show e ++ " -> " ++ show e'
       typeOfMorAtts (att,e) | Map.member att (catts $ m_src mor)
         = let (s,t) = fromJust $ Map.lookup att $ catts $ m_src mor
               s' = transE s
           in do t0 <- typeOf' (m_dst mor) (Map.fromList [(Left (),Right s')]) $ up2 e
                 if t0 == Left t then pure () else Left $ "2Ill typed attribute, " ++ show att ++ " expression " ++ show e
                  ++ ", computed type " ++ show t0 ++ " and required type " ++ show t
       typeOfMorAtts (e,e') = Left $ "Bad att mapping " ++ show e ++ " -> " ++ show e'
       typeOfMorGens (gen,e) | Map.member gen (cgens $ m_src mor)
         = let t = fromJust $ Map.lookup gen $ cgens $ m_src mor
               t' = transE t
           in do t0 <- typeOf' (m_dst mor) (Map.fromList []) $ up e
                 if t0 == Right t' then pure () else Left $ "3Ill typed in " ++ show gen ++ ": " ++ show e
       typeOfMorGens (e,e') = Left $ "Bad gen mapping " ++ show e ++ " -> " ++ show e'
       typeOfMorSks (sk,e) | Map.member sk (csks $ m_src mor)
         = let t = fromJust $ Map.lookup sk $ csks $ m_src mor
           in do t0 <- typeOf' (m_dst mor) (Map.fromList []) $ up4 e
                 if t0 == Left t then pure () else Left $ "4 Ill typed in " ++ show sk ++ ": " ++ show e
       typeOfMorSks (e,e') = Left $ "Bad null mapping " ++ show e ++ " -> " ++ show e'





initGround :: (Ord ty, Ord en) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool)
initGround col = (me', mt')
 where me = Map.fromList $ Prelude.map (\en -> (en, False)) $ Set.toList $ cens col
       mt = Map.fromList $ Prelude.map (\ty -> (ty, False)) $ Set.toList $ ctys col
       me' = Prelude.foldr (\(_, en) m -> Map.insert en True m) me $ Map.toList $ cgens col
       mt' = Prelude.foldr (\(_, ty) m -> Map.insert ty True m) mt $ Map.toList $ csks col


closeGround :: (Ord ty, Ord en) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool) -> (Map en Bool, Map ty Bool)
closeGround col (me, mt) = (me', mt'')
 where mt''= Prelude.foldr (\(_, (tys,ty)) m -> if and (Prelude.map (\ty'->lookup2 ty' mt') tys) then Map.insert ty True m else m) mt' $ Map.toList $ csyms col
       mt' = Prelude.foldr (\(_, (en,ty)) m -> if lookup2 en me' then Map.insert ty True m else m) mt $ Map.toList $ catts col
       me' = Prelude.foldr (\(_, (en,_)) m -> if lookup2 en me then Map.insert en True m else m) me $ Map.toList $ cfks col

iterGround :: (Ord ty, Ord en, Show en, Show ty) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool) -> (Map en Bool, Map ty Bool)
iterGround col r = if r == r' then r else iterGround col r'
 where r' = closeGround col r

computeGround :: (Ord ty, Ord en, Show en, Show ty) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool)
computeGround col = iterGround col $ initGround col

allSortsInhabited :: (Ord ty, Ord en, Show en, Show ty) => Collage var ty sym en fk att gen sk -> Bool
allSortsInhabited col = t && f
 where (me, mt) = computeGround col
       t = and $ Map.elems me
       f = and $ Map.elems mt


-- I've given up on non string based error handling for now
typeOf'
  :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> Ctx var (ty + en)
  -> Term    var ty sym en fk att gen sk
  -> Err (ty + en)
typeOf' _ ctx (Var v) = note ("Unbound variable: " ++ show v) $ Map.lookup v ctx
typeOf' col _ (Gen g) = case Map.lookup g $ cgens col of
  Nothing -> Left $ "Unknown generator: " ++ show g
  Just t -> pure $ Right t
typeOf' col _ (Sk s) = case Map.lookup s $ csks col of
  Nothing -> Left $ "Unknown labelled null: " ++ show s
  Just t -> pure $ Left t
typeOf' col ctx (xx@(Fk f a)) = case Map.lookup f $ cfks col of
  Nothing -> Left $ "Unknown foreign key: " ++ show f
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
                    then if (fmap Left s) == s'
                         then pure $ Left t
                         else Left $ "Expected arguments to have types " ++
                     show s ++ " but given " ++ show s' ++ " in " ++ (show $ xx)
                    else Left $ "Expected argument to have arity " ++
                     show (length s) ++ " but given " ++ show (length s') ++ " in " ++ (show $ xx)

typeOfEq'
  :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> (Ctx var (ty + en), EQ var ty sym en fk att gen sk)
  -> Err (ty + en)
typeOfEq' col (ctx, EQ (lhs, rhs)) = do lhs' <- typeOf' col ctx lhs
                                        rhs' <- typeOf' col ctx rhs
                                        if lhs' == rhs'
                                        then pure lhs'
                                        else Left $ "Equation lhs has type " ++ show lhs' ++ " but rhs has type " ++ show rhs'

checkDoms :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> Err ()
checkDoms col = do
  _ <- mapM f $ Map.elems $ csyms col
  _ <- mapM g $ Map.elems $ cfks  col
  _ <- mapM h $ Map.elems $ catts col
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
  :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> Err ()
typeOfCol col = do checkDoms col
                   _ <- mapM (typeOfEq' col) $ Set.toList $ ceqs col
                   pure ()


data RawTerm = RawApp String [RawTerm]
 deriving Eq

instance Show RawTerm where
 show (RawApp sym az) = show sym ++ "(" ++ (intercalate "," . fmap show $ az) ++ ")"

upTerm
 :: Term var Void Void en fk Void gen Void -> Term var ty sym en fk att gen sk
upTerm
 (Var v) = Var v
upTerm
 (Fk f a) = Fk f $ upTerm a
upTerm
 (Gen g) = Gen g
upTerm
 (Sym f _) = absurd f
upTerm
 (Sk f) = absurd f
upTerm
 (Att f _) = absurd f

--Set is not Traversable! Lame
