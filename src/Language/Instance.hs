{-# LANGUAGE AllowAmbiguousTypes    #-}
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

module Language.Instance where

import qualified Data.Foldable         as Foldable
import           Data.List             hiding (intercalate)
import           Data.Map.Strict       (Map, unionWith)
import qualified Data.Map.Strict       as Map
import           Data.Maybe
import           Data.Set              (Set)
import qualified Data.Set              as Set
import           Data.Typeable         hiding (typeOf)
import           Data.Void
import           Language.Common
import           Language.Mapping      as Mapping
import           Language.Options
import           Language.Prover
import           Language.Query
import           Language.Schema       as Schema
import           Language.Term         as Term
import           Language.Typeside     as Typeside
import           Prelude               hiding (EQ)
import qualified Text.Tabular          as T
import qualified Text.Tabular.AsciiArt as Ascii

emptyInstance :: Schema var ty sym en fk att -> Instance var ty sym en fk att Void Void Void Void
emptyInstance ts'' =
  Instance ts''
           (Presentation Map.empty Map.empty Set.empty)
           (const undefined)
           (Algebra ts''
                    (const Set.empty) (const undefined) (const undefined)
                    (const Set.empty) (const undefined) (const undefined)
                    Set.empty)


evalSchTerm' :: Algebra var ty sym en fk att gen sk x y -> x -> Term () Void Void en fk Void Void Void
 -> x
evalSchTerm' _ x (Var ())   = x
evalSchTerm' alg x (Fk f a) = aFk alg f $ evalSchTerm' alg x a
evalSchTerm' _ _ (Gen g)    = absurd g
evalSchTerm' _ _ (Sk g)     = absurd g
evalSchTerm' _ _ (Sym f _)  = absurd f
evalSchTerm' _ _ _          = undefined

evalSchTerm :: Algebra var ty sym en fk att gen sk x y -> x -> Term () ty sym en fk att Void Void
 -> Term Void ty sym Void Void Void Void y
evalSchTerm alg x (Att f a)  = aAtt alg f $ evalSchTerm' alg x (down1 a)
evalSchTerm _ _ (Sk g)       = absurd g
evalSchTerm alg x (Sym f as) = Sym f $ fmap (evalSchTerm alg x) as
evalSchTerm _ _ _            = undefined




-- return input for convenience
typecheckPresentation
  :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord fk, Ord att, Show fk, Show att, Show en, Ord en, Ord gen, Show gen, Ord sk, Show sk)
  => Schema var ty sym en fk att
  -> Presentation var ty sym en fk att gen sk
  -> Err (Presentation var ty sym en fk att gen sk)
typecheckPresentation sch p = do
  _ <- typeOfCol $ instToCol sch p
  pure p

down1 :: Term x ty sym en fk att gen sk -> Term x Void Void en fk Void gen Void
down1 (Var v)  = Var v
down1 (Gen g)  = Gen g
down1 (Fk f a) = Fk f $ down1 a
down1 _        = undefined

checkSatisfaction
  :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord fk, Ord att, Show fk, Show att, Show en, Ord en, Ord gen, Show gen, Ord sk, Show sk, Ord x, Ord y)
  => Instance var ty sym en fk att gen sk x y
  -> Err ()
checkSatisfaction (Instance sch pres' dp' alg) = do
  _ <- mapM (\(EQ (l, r)) -> if hasTypeType l then h (show l) (show r) (g l r) else h (show l) (show r) (f l r)) $ Set.toList $ eqs0 pres'
  _ <- mapM (\(en'', EQ (l, r)) -> h (show l) (show r) (g' l r en'')) $ Set.toList $ obs_eqs sch
  _ <- mapM (\(en'', EQ (l, r)) -> h (show l) (show r) (f' l r en'')) $ Set.toList $ path_eqs sch
  return ()
  where f l r = nf alg (down1 l) == nf alg (down1 r)
        g l r = dp' $ EQ ((repr'' alg (nf'' alg l)), (repr'' alg (nf'' alg r))) --morally we should create a new dp for the talg, but that's computationally intractable and this check still helps
        h _ _ True  = return ()
        h l r False = Left $ "Not satisified: " ++ l ++ " = " ++ r
        f' l r e = foldr (\x b -> (evalSchTerm' alg x l == evalSchTerm' alg x r) && b) True (en alg e)
        g' l r e = foldr (\x b -> (dp' $ EQ (repr'' alg (evalSchTerm alg x l), repr'' alg (evalSchTerm alg x r))) && b) True (en alg e)

-- x: type of Carrier
-- y: type of generators for type algebra presentation
data Algebra var ty sym en fk att gen sk x y
  = Algebra
  { aschema :: Schema var ty sym en fk att

  , en      :: en -> (Set x) -- globally unique xs
  , nf      :: Term Void Void Void en fk Void gen Void -> x
  , repr    :: x -> Term Void Void Void en fk Void gen Void

  , ty      :: ty -> (Set y) -- globally unique ys
  , nf'     :: sk + (x, att) -> Term Void ty sym Void Void Void Void y
  , repr'   :: y -> Term Void ty sym en fk att gen sk

  , teqs    :: Set (EQ Void ty sym Void Void Void Void y)

  } -- omit Eq, doesn't seem to be necessary for now

simplifyA
  :: ( Ord var, Ord ty, Ord sym, Ord x, Ord y, Ord en, Ord sk, Ord fk, Ord att, Ord gen, Ord x, Ord sk
     , Show var, Show ty, Show sym, Show x, Show y, Show gen, Show sk, Show en, Show sk, Show fk, Show att, Show gen)
  => Algebra var ty sym en fk att gen sk x y
  -> Algebra var ty sym en fk att gen sk x y
simplifyA
  (Algebra sch en' nf''' repr''' ty'  nf''''  repr'''' teqs'   ) =
   Algebra sch en' nf''' repr''' ty'' nf''''' repr'''' teqs''''
   where teqs''       = Set.map (\x -> (Map.empty, x)) teqs'
         (teqs''', f) = simplify'' teqs'' []
         teqs''''     = Set.map snd teqs'''
         ty'' t       = Set.filter (\x -> not $ elem (HSk x) $ fst $ unzip f) $ ty' t
         nf''''' e    = replaceRepeatedly f $ nf'''' e



castX :: Term Void ty sym en fk att gen sk -> Maybe (Term Void Void Void en fk Void gen Void)
castX t = case t of
  Gen g   -> Just $ Gen g
  Fk  f a -> Fk f <$> castX a
  Var v   -> absurd v
  _       -> Nothing

nf'' :: Algebra var ty sym en fk att gen sk x y -> Term Void ty sym en fk att gen sk -> Term Void ty sym Void Void Void Void y
nf'' alg t = case t of
  Sym f as -> Sym f (nf'' alg <$> as)
  Att f a  -> nf' alg $ Right (nf alg (fromJust $ castX a), f)
  Sk  s    -> nf' alg $ Left s
  _        -> undefined

repr'' :: Algebra var ty sym en fk att gen sk x y -> Term Void ty sym Void Void Void Void y -> Term Void ty sym en fk att gen sk
repr'' alg t = case t of
  Sym f as -> Sym f (repr'' alg <$> as)
  Sk  s    -> repr' alg s
  _        -> undefined

aGen :: Algebra var ty sym en fk att gen sk x y -> gen -> x
aGen alg g = nf alg $ Gen g

aFk :: Algebra var ty sym en fk att gen sk x y -> fk -> x -> x
aFk alg f x = nf alg $ Fk f $ repr alg x

aAtt :: Algebra var ty sym en fk att gen sk x y -> att -> x -> Term Void ty sym Void Void Void Void y
aAtt alg f x = nf'' alg $ Att f $ up15 $ repr alg x

aSk :: Algebra var ty sym en fk att gen sk x y -> sk -> Term Void ty sym Void Void Void Void y
aSk alg g = nf'' alg $ Sk g

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Eq en, Eq fk, Eq att)
  => Show (Algebra var ty sym en fk att gen sk x y) where
  show alg@(Algebra sch _ _ _ ty' _ _ teqs') =
    "algebra" ++ "\n" ++
    (intercalate "\n\n" prettyEntities) ++ "\n" ++
    "type-algebra" ++ "\n" ++
    "nulls" ++ "\n" ++
    w ++
    prettyTypeEqns
    where w = "  " ++ (intercalate "\n  " . mapl w2 . Typeside.tys . Schema.typeside $ sch)
          w2 ty'' = show ty'' ++ " (" ++ (show . Set.size $ ty' ty'') ++ ") = " ++ show (Foldable.toList $ ty' ty'') ++ " "

          prettyEntities = prettyEntityTable alg `mapl` Schema.ens sch
          prettyTypeEqns = intercalate "\n" (Set.map show teqs')

prettyEntity
  :: (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Eq en)
  => Algebra var ty sym en fk att gen sk x y
  -> en
  -> String
prettyEntity alg@(Algebra sch en' _ _ _ _ _ _) es =
  show es ++ " (" ++ (show . Set.size $ en' es) ++ ")\n" ++
  "-------------\n" ++
  (intercalate "\n" $ prettyEntityRow es `mapl` en' es)
  where
    -- prettyEntityRow :: en -> x -> String
    prettyEntityRow en'' e =
      show e ++ ": " ++
      intercalate "," (prettyFk  e <$> fksFrom'  sch en'') ++ ", " ++
      intercalate "," (prettyAtt e <$> attsFrom' sch en'')

    -- prettyAtt :: x -> (att, w) -> String
    prettyAtt x (att,_) = show att ++ " = " ++ (prettyTerm $ aAtt alg att x)

    prettyFk  x (fk, _) = show fk  ++ " = " ++ (show $ aFk alg fk x)

    prettyTerm = show

-- TODO unquote identifiers; stick fks and attrs in separate `Group`s?
prettyEntityTable
  :: (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Eq en)
  => Algebra var ty sym en fk att gen sk x y
  -> en
  -> String
prettyEntityTable alg@(Algebra sch en' _ _ _ _ _ _) es =
  show es ++ " (" ++ show (Set.size (en' es)) ++ ")\n" ++
  (Ascii.render show id id tbl)
  where
    -- tbl :: T.Table x String String
    tbl = T.Table
      (T.Group T.SingleLine (T.Header <$> Foldable.toList (en' es)))
      (T.Group T.SingleLine (T.Header <$> prettyColumnHeaders))
      (prettyRow <$> Foldable.toList (en' es))

    prettyColumnHeaders :: [String]
    prettyColumnHeaders =
      (prettyTypedIdent <$> fksFrom' sch es) ++
      (prettyTypedIdent <$> attsFrom' sch es)

    prettyRow e =
      (prettyFk e <$> fksFrom' sch es) ++ (prettyAtt e <$> attsFrom' sch es)

    prettyTypedIdent (ident, typ) = show ident ++ " : " ++ show typ

    prettyFk x (fk, _) = show $ aFk alg fk x

    -- prettyAtt :: x -> (att, w) -> String
    prettyAtt x (att,_) = prettyTerm $ aAtt alg att x

    prettyTerm = show

fksFrom :: Eq en => Collage var ty sym en fk att gen sk -> en -> [(fk,en)]
fksFrom sch en' = f $ Map.assocs $ cfks sch
  where f []               = []
        f ((fk,(en1,t)):l) = if en1 == en' then (fk,t) : (f l) else f l


attsFrom :: Eq en => Collage var ty sym en fk att gen sk -> en -> [(att,ty)]
attsFrom sch en' = f $ Map.assocs $ catts sch
  where f []               = []
        f ((fk,(en1,t)):l) = if en1 == en' then (fk,t) : (f l) else f l


fksFrom' :: Eq en => Schema var ty sym en fk att  -> en -> [(fk,en)]
fksFrom' sch en' = f $ Map.assocs $ Schema.fks sch
  where f []               = []
        f ((fk,(en1,t)):l) = if en1 == en' then (fk,t) : (f l) else f l


attsFrom' :: Eq en => Schema var ty sym en fk att -> en -> [(att,ty)]
attsFrom' sch en' = f $ Map.assocs $ Schema.atts sch
  where f []               = []
        f ((fk,(en1,t)):l) = if en1 == en' then (fk,t) : (f l) else f l

data Presentation var ty sym en fk att gen sk
  = Presentation
  { gens :: Map gen en
  , sks  :: Map sk ty
  , eqs  :: Set (EQ Void ty sym en fk att gen sk)
  }

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk)
  => Show (Presentation var ty sym en fk att gen sk) where
  show (Presentation ens' _ eqs') = "presentation {\n" ++
    "generators\n\t" ++ showCtx' ens' ++ "\n" ++
    "equations\n\t" ++ intercalate "\n\t" (Set.map show eqs') ++ "}"

data Instance var ty sym en fk att gen sk x y
  = Instance
  { schema  :: Schema       var  ty sym en fk att
  , pres    :: Presentation var  ty sym en fk att gen sk
  , dp      :: EQ           Void ty sym en fk att gen sk -> Bool
  , algebra :: Algebra      var  ty sym en fk att gen sk x y
  }

data InstanceEx :: * where
  InstanceEx :: forall var ty sym en fk att gen sk x y.
   (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y,
    Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Ord x, Ord y,
    Typeable var, Typeable ty, Typeable sym, Typeable en, Typeable fk, Typeable att, Typeable gen, Typeable sk, Typeable x, Typeable y) =>
   Instance var ty sym en fk att gen sk x y -> InstanceEx

deriving instance Show (InstanceEx)

instToCol
  :: ( Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en
     , Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk)
  => Schema var ty sym en fk att
  -> Presentation var ty sym en fk att gen sk
  -> Collage (()+var) ty sym en fk att gen sk
instToCol sch (Presentation gens' sks' eqs') =
 Collage (Set.union e1 e2) (ctys schcol)
         (cens schcol) (csyms schcol) (cfks schcol) (catts schcol) gens' sks'
   where schcol = schToCol sch
         e1 = Set.map (\(EQ (l,r)) -> (Map.empty, EQ (up4 l, up4 r))) eqs'
         e2 = Set.map (\(g, EQ (l,r)) -> (g, EQ (up5 l, up5 r))) $ ceqs schcol


up5 :: Term var ty sym en fk att Void Void -> Term var ty sym en fk att gen sk
up5 t = case t of
  Var v   -> Var v
  Sym f x -> Sym f $ up5 <$> x
  Fk  f a -> Fk  f $ up5 a
  Att f a -> Att f $ up5 a
  Gen f   -> absurd f
  Sk  f   -> absurd f

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Eq en, Eq fk, Eq att)
  => Show (Instance var ty sym en fk att gen sk x y) where
  show (Instance _ p _ alg) =
    "instance\n" ++
    show p ++ "\n" ++
    show alg

showCtx' :: (Show a1, Show a2) => Map a1 a2 -> [Char]
showCtx' m = intercalate "\n\t" $ fmap (\(k,v) -> show k ++ " : " ++ show v) $ Map.toList m

-- in java we just use pointer equality.  this is better, but really
-- we want that the intances denote the same set-valued functor,
-- possibly up to natural isomorphism. in practice equality only
-- happens during type checking, so the check below suffices... but
-- hopefully it won't incur a performance penalty.  side note:
-- eventually schema equality will need to be relaxed too.
instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Eq x, Eq y)
  => Eq (Instance var ty sym en fk att gen sk x y) where
  (==) (Instance schema' (Presentation gens' sks' eqs') _ _) (Instance schema'' (Presentation gens'' sks'' eqs'') _ _)
    = (schema' == schema'') && (gens' == gens'') && (sks' == sks'') && (eqs' == eqs'')


-- adds one equation per fact in the algebra.
algebraToPresentation :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk, Ord y, Ord x)
  => Algebra var ty sym en fk att gen sk x y
  -> Presentation var ty sym en fk att x y
algebraToPresentation (alg@(Algebra sch en' _ _ ty' _ _ _)) = Presentation gens' sks' eqs'
 where gens' = Map.fromList $ reify en' $ Schema.ens sch
       sks' = Map.fromList $ reify ty' $ Typeside.tys $ Schema.typeside sch
       eqs1 = concat $ Prelude.map (\(x,en'') -> f x en'') reified
       eqs2 = concat $ Prelude.map (\(x,en'') -> g x en'') reified
       eqs' = Set.fromList $ eqs1 ++ eqs2
       reified = reify en' (Schema.ens sch)
       f x e = Prelude.map (\(fk,_) -> f' x fk) $ fksFrom' sch e
       g x e = Prelude.map (\(att,_) -> g' x att) $ attsFrom' sch e
       f' x fk = EQ (Fk fk (Gen x), Gen $ aFk alg fk x)
       g' x att = EQ (Att att (Gen x), up6 $ aAtt alg att x)



up6 :: Term Void ty sym Void Void Void Void sk -> Term var ty sym en fk att gen sk
up6 (Var v)    = absurd v
up6 (Gen g)    = absurd g
up6 (Sk  s)    = Sk s
up6 (Fk  f _)  = absurd f
up6 (Att f _)  = absurd f
up6 (Sym f as) = Sym f $ Prelude.map up6 as

reify :: (Ord x, Ord en) => (en -> Set x) -> Set en -> [(x, en)]
reify f s = concat $ Set.toList $ Set.map (\en'-> Set.toList $ Set.map (\x->(x,en')) $ f en') $ s


initialInstance :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk)
 => Presentation var ty sym en fk att gen sk -> (EQ (()+var) ty sym en fk att gen sk -> Bool)
 -> Schema var ty sym en fk att ->
 Instance var ty sym en fk att gen sk (Carrier en fk gen) (TalgGen en fk att gen sk)
initialInstance p dp' sch = Instance sch p dp'' $ initialAlgebra p dp' sch
 where dp'' (EQ (lhs, rhs)) = dp' $ EQ (up4 lhs, up4 rhs)

up15 :: Term Void Void Void en fk Void gen Void -> Term Void ty sym en fk att gen sk
up15 = up

initialAlgebra :: (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Ord en,
  Show en, Ord fk, Show fk, Ord att, Show att, Ord gen, Show gen, Ord sk, Show sk)
 => Presentation var ty sym en fk att gen sk
 -> (EQ (()+var) ty sym en fk att gen sk -> Bool)
 -> Schema var ty sym en fk att ->
 Algebra var ty sym en fk att gen sk (Carrier en fk gen) (TalgGen en fk att gen sk)
initialAlgebra p dp' sch = simplifyA this
 where this = Algebra sch en' nf''' repr''' ty' nf'''' repr'''' teqs'
       col = instToCol sch p
       ens'  = assembleGens col (close col dp')
       en' k = lookup2 k ens'
       nf''' e = let t = typeOf col e
                     f []    = undefined -- impossible
                     f (a:b) = if dp' (EQ (up a, up e)) then a else f b
              in f $ Set.toList $ lookup2 t ens'
       repr''' x = x

       tys' = assembleSks col ens'
       ty' y = lookup2 y tys'

       nf'''' (Left g)          = Sk $ MkTalgGen $ Left g
       nf'''' (Right (gt, att)) = Sk $ MkTalgGen $ Right (repr''' gt, att)

       repr'''' :: TalgGen en fk att gen sk -> Term Void ty sym en fk att gen sk
       repr'''' (MkTalgGen (Left g))         = Sk g
       repr'''' (MkTalgGen (Right (x, att))) = Att att $ up15 $ repr''' x

       teqs'' = concatMap (\(e, EQ (lhs,rhs)) -> fmap (\x -> EQ (nf'' this $ subst' x lhs, nf'' this $ subst' x rhs)) (Set.toList $ en' e)) $ Set.toList $ obs_eqs sch
       teqs' = Set.union (Set.fromList teqs'') (Set.map (\(EQ (lhs,rhs)) -> EQ (nf'' this lhs, nf'' this rhs)) (Set.filter hasTypeType' $ eqs0 p))

--created as an alias because of name clashes
eqs0
  :: Presentation var  ty sym en fk att gen sk
  -> Set (EQ      Void ty sym en fk att gen sk)
eqs0 (Presentation _ _ x) = x

subst' :: Carrier en fk gen -> Term () ty sym en fk att Void Void -> Term Void ty sym en fk att gen sk
subst' t s = case s of
  Var ()   -> up t
  Sym fs a -> Sym fs $ subst' t <$> a
  Fk  f  a -> Fk  f  $ subst' t     a
  Att f  a -> Att f  $ subst' t     a
  Gen f    -> absurd f
  Sk  f    -> absurd f

hasTypeType :: Term Void ty sym en fk att gen sk -> Bool
hasTypeType t = case t of
  Var f   -> absurd f
  Sym _ _ -> True
  Att _ _ -> True
  Sk  _   -> True
  Gen _   -> False
  Fk  _ _ -> False

hasTypeType' :: EQ Void ty sym en fk att gen sk -> Bool
hasTypeType' (EQ (lhs, _)) = hasTypeType lhs


fromListAccum :: (Ord v, Ord k) => [(k, v)] -> Map k (Set v)
fromListAccum []          = Map.empty
fromListAccum ((k,v):kvs) = Map.insert k op (fromListAccum kvs)
  where
    op = maybe (Set.singleton v) (Set.insert v) (Map.lookup k r)
    r  = fromListAccum kvs

assembleSks
  :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Show en, Ord en)
  => Collage var ty sym en fk att gen sk
  -> Map en (Set (Carrier en fk gen))
  -> Map ty (Set (TalgGen en fk att gen sk))
assembleSks col ens' = unionWith Set.union sks' $ fromListAccum gens'
 where
   gens' = concatMap (\(en',set) -> concatMap (\term -> concatMap (\(att,ty') -> [(ty',(MkTalgGen . Right) (term,att))]) $ attsFrom col en') $ Set.toList $ set) $ Map.toList $ ens'
   sks'  = foldr (\(sk,t) m -> Map.insert t (Set.insert (MkTalgGen . Left $ sk) (lookup2 t m)) m) ret $ Map.toList $ csks col
   ret   = Map.fromSet (const Set.empty) $ ctys col


type Carrier en fk gen = Term Void Void Void en fk Void gen Void

-- | T means type. This can be either a labeled null (`sk`) or... a proper value
-- | This type allows us to define e.g. a custom Show instance.
newtype TalgGen en fk att gen sk = MkTalgGen (Either sk (Carrier en fk gen, att))

instance (Show en, Show fk, Show att, Show gen, Show sk) => Show (TalgGen en fk att gen sk) where
  show (MkTalgGen (Left  x)) = show x
  show (MkTalgGen (Right x)) = show x

deriving instance (Ord en, Ord fk, Ord att, Ord gen, Ord sk) => Ord (TalgGen en fk att gen sk)

deriving instance (Eq en, Eq fk, Eq att, Eq gen, Eq sk) => Eq (TalgGen en fk att gen sk)

assembleGens :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en)
 => Collage var ty sym en fk att gen sk -> [Carrier en fk gen] -> Map en (Set (Carrier en fk gen))
assembleGens col [] = Map.fromList $ Prelude.map (\x -> (x,Set.empty)) $ Set.toList $ cens col
assembleGens col (e:tl) = Map.insert t (Set.insert e s) m
 where m = assembleGens col tl
       t = typeOf col e
       s = fromJust $ Map.lookup t m

close
  :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en)
  => Collage var  ty   sym  en fk att  gen sk
  -> (EQ     var  ty   sym  en fk att  gen sk    -> Bool)
  -> [Term   Void Void Void en fk Void gen Void]
close col dp' =
  y (close1m dp' col) $ fmap Gen $ Map.keys $ cgens col
  where
    y f x = let z = f x in if x == z then x else y f z

close1m :: (Foldable t, Show var, Show gen, Show sk, Show fk,
                  Show en, Show ty, Show att, Show sym, Ord var, Ord gen, Ord sk,
                  Ord fk, Ord en, Ord ty, Ord att, Ord sym) =>
                 (EQ var ty sym en fk att gen sk -> Bool)
                 -> Collage var ty sym en fk att gen sk
                 -> t (Term Void Void Void en fk Void gen Void)
                 -> [Term Void Void Void en fk Void gen Void]
close1m dp' col = dedup dp' . concatMap (close1 col dp')

dedup :: (EQ var ty sym en fk att gen sk -> Bool)
               -> [Term Void Void Void en fk Void gen Void]
               -> [Term Void Void Void en fk Void gen Void]
dedup dp' = nubBy (\x y -> dp' (EQ (up x, up y)))

close1 :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en)
 => Collage var ty sym en fk att gen sk -> (EQ var ty sym en fk att gen sk -> Bool) -> Term Void Void Void en fk Void gen Void -> [ (Term Void Void Void en fk Void gen Void) ]
close1 col _ e = e:(fmap (\(x,_) -> Fk x e) l)
 where t = typeOf col e
       l = fksFrom col t



typeOf :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym, Eq en)
  => Collage var ty sym en fk att gen sk -> Term Void Void Void en fk Void gen Void -> en
typeOf col e = case typeOf' col Map.empty (up e) of
  Left _ -> undefined
  Right x -> case x of
               Left _  -> undefined
               Right y -> y



--------------------------------------------------------------------------------


data InstanceExp where
  InstanceVar     :: String                                          -> InstanceExp
  InstanceInitial :: SchemaExp                                       -> InstanceExp

  InstanceDelta   :: MappingExp -> InstanceExp -> [(String, String)] -> InstanceExp
  InstanceSigma   :: MappingExp -> InstanceExp -> [(String, String)] -> InstanceExp
  InstancePi      :: MappingExp -> InstanceExp                       -> InstanceExp

  InstanceEval    :: QueryExp   -> InstanceExp                       -> InstanceExp
  InstanceCoEval  :: MappingExp -> InstanceExp                       -> InstanceExp

  InstanceRaw     :: InstExpRaw'                                     -> InstanceExp
  deriving (Eq,Show)

data InstExpRaw' =
  InstExpRaw'
  { instraw_schema  :: SchemaExp
  , instraw_gens    :: [(String, String)]
--, instraw_sks     :: [(String, String)] this should maybe change in aql grammar
  , instraw_oeqs    :: [(RawTerm, RawTerm)]
  , instraw_options :: [(String, String)]
  , instraw_imports :: [InstanceExp]
} deriving (Eq,Show)

type Gen = String
type Sk = String

conv' :: (Typeable ty,Show ty) => [(String, String)] -> Err [(String, ty)]
conv' [] = pure []
conv' ((att,ty'):tl) = case cast ty' of
   Just ty'' -> do x <- conv' tl
                   return $ (att, ty''):x
   Nothing -> Left $ "Not in schema/typeside: " ++ show ty'


split' :: [(a, Either b1 b2)] -> ([(a, b1)], [(a, b2)])
split' []           = ([],[])
split' ((w, ei):tl) =
  let (a,b) = split' tl
  in case ei of
    Left  x -> ((w,x):a, b      )
    Right x -> (      a, (w,x):b)


split'' :: (Typeable en, Typeable ty, Eq ty, Eq en) => [en] -> [ty] -> [(a, String)] -> Err ([(a, en)], [(a, ty)])
split'' _     _   []           = return ([],[])
split'' ens2 tys2 ((w, ei):tl) =
  do (a,b) <- split'' ens2 tys2 tl
     if elem' ei ens2
     then return ((w, fromJust $ cast ei):a, b)
     else if elem' ei tys2
          then return (a, (w, fromJust $ cast ei):b)
          else Left $ "Not an entity or type: " ++ show ei

evalInstanceRaw'
  :: forall var ty sym en fk att
  .  (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Typeable sym, Typeable ty, Ord en, Typeable fk, Typeable att, Ord fk, Typeable en, Show fk, Ord att, Show att, Show fk, Show en)
  => Schema var ty sym en fk att -> InstExpRaw' -> [Presentation var ty sym en fk att Gen Sk] -> Err (Presentation var ty sym en fk att Gen Sk)
evalInstanceRaw' sch (InstExpRaw' _ gens0 eqs' _ _) is = do
  (gens', sks') <- split'' (Set.toList $ Schema.ens sch) (Set.toList $ tys $ typeside sch) gens0
  gens''        <- toMapSafely gens'
  gens'''       <- return $ Map.toList gens''
  sks''         <- toMapSafely sks'
  sks'''        <- return $ Map.toList sks''
  let gensX = concatMap (Map.toList . gens) is ++ gens'''
      sksX  = concatMap (Map.toList . sks ) is ++ sks'''
  eqs'' <- f gensX sksX eqs'
  return $ Presentation (Map.fromList gensX) (Map.fromList sksX) $ Set.fromList $ (concatMap (Set.toList . eqs0) is) ++ (Set.toList eqs'')
  where
  keys' = fst . unzip

--f :: [(String, String, RawTerm, RawTerm)] -> Err (Set (En, EQ () ty   sym  en fk att  Void Void))
  f _ _ [] = pure $ Set.empty
  f gens' sks' ((lhs, rhs):eqs'') = do lhs' <- g (keys' gens') (keys' sks') lhs
                                       rhs' <- g (keys' gens') (keys' sks') rhs
                                       rest <- f gens' sks' eqs''
                                       pure $ Set.insert (EQ (lhs', rhs')) rest

--g' :: [String] -> RawTerm -> Err (Term Void Void Void en fk Void Gen Void)
  g' gens' (RawApp x [])     | elem x gens'                         = pure $ Gen x
  g' gens' (RawApp x (a:[])) | elem' x (Map.keys $ sch_fks sch)     = do a' <- g' gens' a
                                                                         case cast x :: Maybe fk of
                                                                           Just x' -> return $ Fk x' a'
                                                                           Nothing -> undefined
  g' _     x                                                        = Left $ "cannot type " ++ show x

  g :: [String] -> [String] -> RawTerm -> Err (Term Void ty sym en fk att Gen Sk)
  g gens' _    (RawApp x [])     | elem x gens'                     = pure $ Gen x
  g _     sks' (RawApp x [])     | elem x sks'                      = pure $ Sk x
  g gens' _    (RawApp x (a:[])) | elem' x (Map.keys $ sch_fks sch) = case cast x of
                                                                        Just x' -> Fk x' <$> g' gens' a
                                                                        Nothing -> undefined
  g gens' _    (RawApp x (a:[])) | elem' x (Map.keys $ sch_atts sch) = do a' <- g' gens' a
                                                                          case cast x of
                                                                            Just x' -> Right $ Att x' a'
                                                                            Nothing -> undefined
  g gens' sks' (RawApp v l)                                          = do l' <- mapM (g gens' sks') l
                                                                          case cast v :: Maybe sym of
                                                                            Just x -> Right $ Sym x l'
                                                                            Nothing -> Left $ "Cannot type: " ++ v

evalInstanceRaw :: forall var ty sym en fk att.
 (Ord var, Ord ty, Ord sym, Show var, Show ty, Show sym, Typeable sym, Typeable ty, Ord en, Typeable fk, Typeable att, Ord fk, Typeable en, Show fk, Ord att, Show att, Show fk, Show en, Typeable var)
  => Schema var ty sym en fk att -> InstExpRaw' -> [InstanceEx] -> Err InstanceEx
evalInstanceRaw ty' t is =
 do (i :: [Presentation var ty sym en fk att Gen Sk]) <- g is
    r <- evalInstanceRaw' ty' t i
    _ <- typecheckPresentation ty' r
    l <- toOptions $ instraw_options t
    p <- createProver (instToCol ty' r) l
    pure $ InstanceEx $ initialInstance r (f p) ty'
 where
   f p (EQ (l,r)) = prove p (Map.fromList []) (EQ (l,  r))
   --g :: forall var ty sym en fk att gen sk. (Typeable var, Typeable ty, Typeable sym, Typeable en, Typeable fk, Typeable att, Typeable gen, Typeable sk)
    -- => [InstanceEx] -> Err [Presentation var ty sym en fk att gen sk]
   g [] = return []
   g ((InstanceEx ts):r) = case cast (pres ts) of
                            Nothing -> Left "Bad import"
                            Just ts' -> do r'  <- g r
                                           return $ (ts') : r'




----------------------------------------------------------------------------------

subs
  :: forall var ty sym en fk att en' fk' att' gen sk
  .  ( Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq en'
     , Ord fk', Ord att', Show var, Show att', Show fk', Show sym, Ord en'
     , Show en, Show en', Show ty, Show sym, Show var, Show fk, Show fk', Show att, Show att', Show gen, Show sk)
  => Mapping var ty sym en fk att en' fk' att'
  -> Presentation var ty sym en  fk  att  gen sk
  -> Presentation var ty sym en' fk' att' gen sk
subs (Mapping _ _ ens' fks' atts') (Presentation gens' sks' eqs') = Presentation gens'' sks' eqs''
 where gens'' = Map.map (\k -> fromJust $ Map.lookup k ens') gens'
       eqs''  = Set.map (\(EQ (l, r)) -> EQ (changeEn fks' atts' l, changeEn fks' atts' r)) eqs'


changeEn
  :: (Ord k1, Ord k2, Eq var)
  => Map k1 (Term () Void Void en1 fk Void Void Void)
  -> Map k2 (Term () ty1  sym  en1 fk att  Void Void)
  -> Term Void ty2 sym en2 k1 k2 gen sk
  -> Term var ty1 sym en1 fk att gen sk
changeEn fks' atts' t = case t of
  Var v    -> absurd v
  Sym h as -> Sym h $ changeEn fks' atts' <$> as
  Sk k     -> Sk k
  Gen g    -> Gen g
  Fk h a   -> subst (up13 $ fromJust $ Map.lookup h fks')  $ changeEn fks' atts' a
  Att h a  -> subst (up5  $ fromJust $ Map.lookup h atts') $ changeEn fks' atts' a

changeEn'
  :: (Ord k, Eq var)
  => Map k (Term () Void Void en1 fk Void Void Void)
  -> t
  -> Term Void ty1 Void en2 k Void gen Void
  -> Term var ty2 sym en1 fk att gen sk
changeEn' fks' atts' t = case t of
  Var v   -> absurd v
  Sym h _ -> absurd h
  Sk k    -> absurd k
  Gen g   -> Gen g
  Fk h a  -> subst (up13 $ fromJust $ Map.lookup h fks') $ changeEn' fks' atts' a
  Att h _ -> absurd h

evalSigmaInst
  :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y, Eq en',
      Ord fk', Ord att', Show var, Show att', Show fk', Show sym, Ord en',
      Show en, Show en', Show ty, Show sym, Show var, Show fk, Show fk', Show att, Show att',
      Show gen, Show sk )
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en fk att gen sk x y -> Options
  -> Err (Instance var ty sym en' fk' att' gen sk (Carrier en' fk' gen) (TalgGen en' fk' att' gen sk))
evalSigmaInst f i o = do d <- createProver (instToCol s p) o
                         return $ initialInstance p (\(EQ (l,r)) -> prove d Map.empty (EQ (l,r))) s
 where p = subs f $ pres i
       s = dst f

mapGen :: (t1 -> t2) -> Term var ty sym en (t2 -> t2) att t1 sk -> t2
mapGen f (Gen g)   = f g
mapGen f (Fk fk a) = fk $ mapGen f a
mapGen _ _         = undefined

evalDeltaAlgebra
  :: forall var ty sym en fk att gen sk x y en' fk' att'
   . ( Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Show en', Show fk', Show att'
     , Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Ord x, Ord y, Ord en', Ord fk', Ord att')
  => Mapping  var ty sym en  fk  att  en'       fk' att'
  -> Instance var ty sym en' fk' att' gen       sk  x       y
  -> Algebra  var ty sym en  fk  att  (en, x)   y   (en, x) y
evalDeltaAlgebra (Mapping src' _ ens' fks0 atts0)
  (Instance _ _ _ (alg@(Algebra _ en' nf''' repr''' ty' _ _ teqs')))
  = Algebra src' en'' nf''x repr'''' ty' nf'''' repr''''' teqs'
 where en'' e = Set.map (\x -> (e,x)) $ en' $ fromJust $ Map.lookup e ens'
       nf''x :: Term Void Void Void en fk Void (en,x) Void -> (en, x)
       nf''x (Gen g) = g
       nf''x (Fk f a) = let (_,x) = nf''x a
                       in (snd $ fromJust $ Map.lookup f $ Schema.fks src',
                           nf''' $ subst (up13 $ fromJust $ Map.lookup f fks0) (repr''' x) )
       nf''x _ = undefined
       repr'''' :: (en, x) -> Term Void Void Void en fk Void (en, x) Void
       repr'''' (en''', x) = Gen (en''', x)
       repr''''' :: y -> Term Void ty sym en fk att (en,x) y
       repr''''' y = Sk y
       nf'''' :: y + ((en,x), att) -> Term Void ty sym Void Void Void Void y
       nf'''' (Left y) = Sk y
       nf'''' (Right ((_,x), att)) =
         nf'' alg $ subst (q $ fromJust $ Map.lookup att atts0) (p $ repr''' x)
       p :: Term Void Void Void en' fk' Void gen Void -> Term Void ty sym  en' fk' att' gen sk
       p = up
       q :: Term () ty sym en' fk' att' Void Void -> Term () ty sym en' fk' att' gen sk
       q = up5


evalDeltaInst
  :: forall var ty sym en fk att gen sk x y en' fk' att'
   . ( Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Show en', Show fk', Show att'
     , Ord var, Ord  ty, Ord  sym, Ord  en, Ord  fk, Ord  att, Ord  gen, Ord  sk, Ord  x, Ord  y, Ord  en', Ord  fk', Ord  att')
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en' fk' att' gen sk x y -> Options
  -> Err (Instance var ty sym en fk att (en,x) y (en,x) y)
evalDeltaInst m i _ =
  pure $ Instance (src m) p eq' j
  where
    j = evalDeltaAlgebra m i
    p = algebraToPresentation j
    eq' (EQ (l, r)) = dp i $ EQ (f l, f r)

    f :: Term Void ty sym en  fk  att (en, x) y
      -> Term Void ty sym en' fk' att' gen    sk
    f t = case t of
      Var v      -> absurd v
      Sym s'  as -> Sym s' $ f <$> as
      Fk  fk  a  -> subst (up13 $ fromJust $ Map.lookup fk  (Mapping.fks  m)) $ f a
      Att att a  -> subst (up5  $ fromJust $ Map.lookup att (Mapping.atts m)) $ f a
      Gen (_, x) -> up12 $ repr  (algebra i) x
      Sk  y      ->        repr' (algebra i) y
