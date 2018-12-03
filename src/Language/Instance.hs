{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitForAll        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.Instance where

import           Control.DeepSeq
import qualified Data.Foldable         as Foldable
import           Data.List as List            hiding (intercalate)
import           Data.Map.Strict       (Map, member, unionWith, (!))
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
import           Control.Monad


--------------------------------------------------------------------------------------------------------------------
-- Algebras

-- | An algebra (model) of a schema.  For entities, consists of a carrier set, evaluation function
-- (nf), and its "inverse" repr.  For types, consists of a generating set of labelled nulls,
-- evaluation function (nf'), and its "inverse" repr', as well as a set of equations (the so-called type algebra).
-- The Eq instance is not defined because for now we define instance equality to be based on equations.
-- x: type of Carrier
-- y: type of generators for type algebra presentation
data Algebra var ty sym en fk att gen sk x y
  = Algebra
  { aschema :: Schema var ty sym en fk att

  , en      :: en -> (Set x) -- globally unique xs
  , aGen    :: gen -> x
  , aFk     :: fk  -> x -> x
  , repr    :: x   -> Term Void Void Void en fk Void gen Void

  , ty      :: ty -> (Set y) -- globally unique ys
  , nf'     :: sk + (x, att) -> Term Void ty sym Void Void Void Void y
  , repr'   :: y -> Term Void ty sym en fk att gen sk

  , teqs    :: Set (EQ Void ty sym Void Void Void Void y)
  }

instance (NFData var, NFData ty, NFData sym, NFData en, NFData fk, NFData att, NFData x, NFData y)
  => NFData (Algebra var ty sym en fk att gen sk x y)
  where
    rnf (Algebra s0 e0 nf0 nf02 repr0 ty0 nf1 repr1 eqs1) = deepseq s0 $ f e0 $ deepseq nf0 $ deepseq repr0
      $ w ty0 $ deepseq nf1 $ deepseq repr1 $ deepseq nf02 $ rnf eqs1
      where
        f g = deepseq (Set.map (rnf . g) $ Schema.ens s0)
        w g = deepseq (Set.map (rnf . g) $ tys (typeside s0))

-- | Evaluate an entity-side schema term with one free variable, given a value for that variable.
evalSchTerm' :: Algebra var ty sym en fk att gen sk x y -> x -> Term () Void Void en fk Void Void Void -> x
evalSchTerm' alg x term = case term of
  Var _   -> x
  Fk  f a -> aFk alg f $ evalSchTerm' alg x a
  Gen g   -> absurd g
  Sk  g   -> absurd g
  Sym f _ -> absurd f
  Att f _ -> absurd f

-- | Evaluate a type-side schema term with one free variable, given a value for that variable.
evalSchTerm :: Algebra var ty sym en fk att gen sk x y -> x -> Term () ty sym en fk att Void Void
  -> Term Void ty sym Void Void Void Void y
evalSchTerm alg x term = case term of
  Att f a  -> aAtt alg f $ evalSchTerm' alg x $ down1 a
  Sk  g    -> absurd g
  Sym f as -> Sym f $ fmap (evalSchTerm alg x) as
  _        -> error "Impossibility in evalSchTerm, please report.  Given a term of non-type sort."


-- | Helper function used by checkSatisfaction to convert terms in the Collage of entity sort
-- into terms with Voids in the attribute etc slots.  Morally Collage should store two or more
-- classes of equation, but having to convert like this is relatively rare.  Indeed, checkSatisfaction
-- itself is redundant - a properly functioning AQL would not generate unsatisfying instances.
down1 :: Term x ty sym en fk att gen sk -> Term x Void Void en fk Void gen Void
down1 (Var v)  = Var v
down1 (Gen g)  = Gen g
down1 (Fk f a) = Fk f $ down1 a
down1 _        = error "Anomaly: please report.  Function name: down1."

-- | Checks that an instance satisfies its schema.
checkSatisfaction
  :: (Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Ord x)
  => Instance var ty sym en fk att gen sk x y
  -> Err ()
checkSatisfaction (Instance sch pres' dp' alg) = do
  _ <- mapM (\(EQ (l, r)) -> if hasTypeType l then report (show l) (show r) (instEqT l r) else report (show l) (show r) (instEqE l r)) $ Set.toList $ eqs0 pres'
  _ <- mapM (\(en'', EQ (l, r)) -> report (show l) (show r) (schEqT l r en'')) $ Set.toList $ obs_eqs sch
  _ <- mapM (\(en'', EQ (l, r)) -> report (show l) (show r) (schEqE l r en'')) $ Set.toList $ path_eqs sch
  return ()
  where
    instEqE l r = nf alg (down1 l) == nf alg (down1 r)
    instEqT l r = dp' $ EQ ((repr'' alg (nf'' alg l)), (repr'' alg (nf'' alg r))) --morally we should create a new dp for the talg, but that's computationally intractable and this check still helps
    report _ _ True  = return ()
    report l r False = Left $ "Not satisified: " ++ l ++ " = " ++ r
    schEqE l r e = foldr (\x b -> (evalSchTerm' alg x l == evalSchTerm' alg x r) && b) True (en alg e)
    schEqT l r e = foldr (\x b -> (dp' $ EQ (repr'' alg (evalSchTerm alg x l), repr'' alg (evalSchTerm alg x r))) && b) True (en alg e)


-- | Evaluates a type side term to a term in the type algebra.  Crashes if given a term of entity sort.
nf'' :: Algebra var ty sym en fk att gen sk x y -> Term Void ty sym en fk att gen sk -> Term Void ty sym Void Void Void Void y
nf'' alg t = case t of
  Sym f as -> Sym f (nf'' alg <$> as)
  Att f a  -> nf' alg $ Right (nf alg (down1 a), f)
  Sk  s    -> nf' alg $ Left s
  _        -> error "Impossible, please report. Non typeside term passed to nf''."

-- | Evaluates a entity side term to a carrier.  Crashes if given a term of type sort.
nf :: Algebra var ty sym en fk att gen sk x y -> Term Void ty' sym' en fk att' gen sk' -> x
nf alg (Gen g  ) = aGen alg g
nf alg (Fk  f a) = aFk  alg f $ nf alg a
nf _ _ = error "Impossible, error in nf"

-- | "Reverse evaluates" a type algebra term to a term in instance.
repr'' :: Algebra var ty sym en fk att gen sk x y -> Term Void ty sym Void Void Void Void y -> Term Void ty sym en fk att gen sk
repr'' alg t = case t of
  Sym f as -> Sym f (repr'' alg <$> as)
  Sk  s    -> repr' alg s
  Gen g    -> absurd g
  Att a _  -> absurd a
  Fk  f _  -> absurd f
  Var v    -> absurd v

-- | Evaluates an attribute on a value.
aAtt :: Algebra var ty sym en fk att gen sk x y -> att -> x -> Term Void ty sym Void Void Void Void y
aAtt alg f x = nf'' alg $ Att f $ upp $ repr alg x

-- | Evaluates a labelled null.
aSk :: Algebra var ty sym en fk att gen sk x y -> sk -> Term Void ty sym Void Void Void Void y
aSk alg g = nf'' alg $ Sk g


-------------------------------------------------------------------------------------------------------------------

-- | A presentation of an instance.
data Presentation var ty sym en fk att gen sk
  = Presentation
  { gens :: Map gen en
  , sks  :: Map sk ty
  , eqs  :: Set (EQ Void ty sym en fk att gen sk)
  }

instance (NFData ty, NFData sym, NFData en, NFData fk, NFData att, NFData gen, NFData sk)
  => NFData (Presentation var ty sym en fk att gen sk) where
  rnf (Presentation g s e) = deepseq g $ deepseq s $ rnf e

-- | Checks that an instance presentation is a well-formed theory.
typecheckPresentation
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Schema var ty sym en fk att
  -> Presentation var ty sym en fk att gen sk
  -> Err ()
typecheckPresentation sch p = typeOfCol $ presToCol sch p

--created as an alias because of name clashes
eqs0
  :: Presentation var  ty sym en fk att gen sk
  -> Set (EQ      Void ty sym en fk att gen sk)
eqs0 (Presentation _ _ x) = x

-- | Converts a presentation to a collage.
presToCol
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Schema var ty sym en fk att
  -> Presentation var ty sym en fk att gen sk
  -> Collage (()+var) ty sym en fk att gen sk
presToCol sch (Presentation gens' sks' eqs') =
 Collage (Set.union e1 e2) (ctys schcol)
         (cens schcol) (csyms schcol) (cfks schcol) (catts schcol) gens' sks'
  where
    schcol = schToCol sch
    e1 = Set.map (\(   EQ (l,r)) -> (Map.empty, EQ (upp l, upp r)))   eqs'
    e2 = Set.map (\(g, EQ (l,r)) -> (g,         EQ (upp l, upp r))) $ ceqs schcol

-- | A database instance on a schema.  Contains a presentation, an algebra, and a decision procedure.
data Instance var ty sym en fk att gen sk x y
  = Instance
  { schema  :: Schema       var  ty sym en fk att
  , pres    :: Presentation var  ty sym en fk att gen sk
  , dp      :: EQ           Void ty sym en fk att gen sk -> Bool
  , algebra :: Algebra      var  ty sym en fk att gen sk x y
  }

-- | True if the type algebra is empty, which approximates it being free,
-- which approximates it being conservative over the typeside.
freeTalg :: Instance var ty sym en fk att gen sk x y -> Bool
freeTalg (Instance _ _ _ (Algebra _ _ _ _ _ _ _ _ teqs)) = Prelude.null teqs

-- | Just syntactic equality of the theory for now.
instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Eq x, Eq y)
  => Eq (Instance var ty sym en fk att gen sk x y) where
  (==) (Instance schema' (Presentation gens' sks' eqs') _ _) (Instance schema'' (Presentation gens'' sks'' eqs'') _ _)
    = (schema' == schema'') && (gens' == gens'') && (sks' == sks'') && (eqs' == eqs'')

instance (NFData var, NFData ty, NFData sym, NFData en, NFData fk, NFData att, NFData gen, NFData sk, NFData x, NFData y)
  => NFData (Instance var ty sym en fk att gen sk x y) where
  rnf (Instance s0 p0 dp0 a0) = deepseq s0 $ deepseq p0 $ deepseq dp0 $ rnf a0

-- | A dynamically typed instance.
data InstanceEx :: * where
  InstanceEx
    :: forall var ty sym en fk att gen sk x y
    .  (ShowOrdTypeableN '[var, ty, sym, en, fk, att, gen, sk, x, y])
    => Instance var ty sym en fk att gen sk x y
    -> InstanceEx


-- | Converts an algebra into a presentation: adds one equation per fact in the algebra
-- and one generator per element.  Presentations in this form are called saturated because
-- they are maximally large without being redundant.  @I(fk.x) = I(fk)(I(x))@
algebraToPresentation :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk], Ord y, Ord x)
  => Algebra var ty sym en fk att gen sk x y
  -> Presentation var ty sym en fk att x y
algebraToPresentation (alg@(Algebra sch en' _ _ _ ty' _ _ _)) = Presentation gens' sks' eqs'
  where
    gens'   = Map.fromList $ reify en' $ Schema.ens sch
    sks'    = Map.fromList $ reify ty' $ Typeside.tys $ Schema.typeside sch
    eqs1    = concat $ Prelude.map fksToEqs  reified
    eqs2    = concat $ Prelude.map attsToEqs reified
    eqs'    = Set.fromList $ eqs1 ++ eqs2
    reified = reify en' $ Schema.ens sch
    fksToEqs  (x, e) = Prelude.map (\(fk , _) -> fkToEq  x fk ) $ fksFrom'  sch e
    attsToEqs (x, e) = Prelude.map (\(att, _) -> attToEq x att) $ attsFrom' sch e
    fkToEq  x fk  = EQ (Fk fk   (Gen x), Gen $ aFk  alg fk  x)
    attToEq x att = EQ (Att att (Gen x), upp $ aAtt alg att x)

reify :: (Ord x, Ord en) => (en -> Set x) -> Set en -> [(x, en)]
reify f s = concat $ Set.toList $ Set.map (\en'-> Set.toList $ Set.map (\x->(x,en')) $ f en') $ s

-- | Constructs an algebra from a saturated theory with a free type algebra.
-- Needs to have satisfaction checked.
saturatedInstance
  :: forall var ty sym en fk att gen sk
  .  (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Schema var ty sym en fk att
  -> Presentation var ty sym en fk att gen sk
  -> Err (Instance var ty sym en fk att gen sk gen (Either sk (gen, att)))
saturatedInstance sch (Presentation gens sks eqs) = do
  (fks, atts) <- foldM procEq (Map.empty, Map.empty) eqs
  checkTotality fks
  _ <- if Set.null (Typeside.eqs $ typeside sch) then return () else Left "Typeside must be free"
  let alg = Algebra sch (Set.fromList . gens') (nf1 fks) (nf2 fks) Gen (Set.fromList . (sks' atts)) (nf' atts) repr' Set.empty
  pure $ Instance sch (Presentation gens sks eqs) (\(EQ (l, r)) -> l == r) alg
  where
    --checkTotality :: Map (gen, fk) gen -> Err ()
    checkTotality fks =
      mapM_ (\en -> if (List.null (fksMissing en fks))
                    then pure ()
                    else Left $ "Missing equation for " ++ show en) $ Schema.ens sch

    fksMissing  en fks  = [ gen | gen <- gens' en, (fk,  _) <- fksFrom'  sch en, not $ member (gen, fk ) fks  ]

    gens' en = [ gen | (gen, en') <- Map.toList gens, en == en' ]

    sks'  atts ty = [ Left sk  | (sk , ty') <- Map.toList sks , ty == ty' ] ++
      [ Right (gen, att) | enX :: en <- Set.toList (Schema.ens sch), gen <- gens' enX, (att, t) <- attsFrom' sch (enX :: en), not (member (gen, att) atts), t == ty ]

    --diff = sks'' en ty \\ atts
    repr' (Left g)         = Sk g
    repr' (Right (x, att)) = Att att $ Gen x

    procEq (fks, atts) (EQ (Fk fk (Gen gen), Gen gen')) = case Map.lookup (gen, fk) fks  of
      Nothing    -> pure (Map.insert (gen, fk) gen' fks, atts)
      Just gen'' -> Left $ "Duplicate binding: " ++ show gen ++ " and " ++ show gen''

    procEq (fks, atts) (EQ (Att att (Gen gen), w)) | isJust p  = case Map.lookup (gen, att) atts of
      Nothing    -> pure (fks, Map.insert (gen, att) (fromJust p) atts)
      Just gen'' -> Left $ "Duplicate binding: " ++ show gen ++ " and " ++ show gen''
      where
        p = case w of
          Sk s -> Just $ Sk $ Left s
          Sym s [] -> Just $ Sym s []
          _ -> Nothing

    procEq _ (EQ (l, r)) = Left $ "Bad eq: " ++ show l ++ " = " ++ show r

    nf1 _ g = g
    nf2 fks f a = fks ! (a, f)

    nf' _    (Left  sk) = Sk $ Left sk
    nf' atts (Right x ) = Map.findWithDefault (Sk (Right x)) x atts


---------------------------------------------------------------------------------------------------------------
-- Initial algebras

type Carrier en fk gen = Term Void Void Void en fk Void gen Void
newtype TalgGen en fk att gen sk = MkTalgGen (Either sk (Carrier en fk gen, att))

-- | Computes an initial instance (minimal model of a presentation).
-- Actually, computes the cannonical term model, where the underlying elements
-- of the carriers are equivalence class of terms modulo provable equality
-- in the presentation (differs from AQL java, which uses fresh IDs).
-- The term model is constructed by repeatedly adding news terms to the empty model
-- until a fixedpoint is reached.
initialInstance
  :: (ShowOrdN '[ var, ty, sym, en, fk, att, gen, sk])
  => Presentation var  ty  sym  en  fk  att  gen  sk
  -> (EQ    (() + var) ty  sym  en  fk  att  gen  sk -> Bool)
  -> Schema       var  ty  sym  en  fk  att
  -> Instance     var  ty  sym  en  fk  att  gen  sk (Carrier en fk gen) (TalgGen en fk att gen sk)
initialInstance p dp' sch = Instance sch p dp'' $ initialAlgebra
  where
    dp'' (EQ (lhs, rhs)) = dp' $ EQ (upp lhs, upp rhs)
    initialAlgebra = simplifyAlg this
    this  = Algebra sch en' nf''' nf'''2 id ty' nf'''' repr'''' teqs'
    col   = presToCol sch p
    ens'  = assembleGens col (close col dp')
    en' k = ens' ! k

    nf'''    e = nf'''_old $ Gen e
    nf'''2 f e = nf'''_old $ Fk  f e
    nf'''_old e = let
      t = typeOf col e
      f []    = error "impossible, please report"
      f (a:b) = if dp' (EQ (upp a, upp e)) then a else f b
      in f $ Set.toList $ ens' ! t

    tys' = assembleSks col ens'
    ty' y =  tys' ! y

    nf'''' (Left g)          = Sk $ MkTalgGen $ Left   g
    nf'''' (Right (gt, att)) = Sk $ MkTalgGen $ Right (gt, att)

    --repr'''' :: TalgGen en fk att gen sk -> Term Void ty sym en fk att gen sk
    repr'''' (MkTalgGen (Left g))         = Sk g
    repr'''' (MkTalgGen (Right (x, att))) = Att att $ upp x

    teqs'' = concatMap (\(e, EQ (lhs,rhs)) -> fmap (\x -> EQ (nf'' this $ subst' lhs x, nf'' this $ subst' rhs x)) (Set.toList $ en' e)) $ Set.toList $ obs_eqs sch
    teqs' = Set.union (Set.fromList teqs'') (Set.map (\(EQ (lhs,rhs)) -> EQ (nf'' this lhs, nf'' this rhs)) (Set.filter hasTypeType' $ eqs0 p))


assembleSks
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Map en (Set (Carrier en fk gen))
  -> Map ty (Set (TalgGen en fk att gen sk))
assembleSks col ens' = unionWith Set.union sks' $ fromListAccum gens'
 where
   gens' = concatMap (\(en',set) -> concatMap (\term -> concatMap (\(att,ty') -> [(ty',(MkTalgGen . Right) (term,att))]) $ attsFrom col en') $ Set.toList $ set) $ Map.toList $ ens'
   sks'  = foldr (\(sk,t) m -> Map.insert t (Set.insert (MkTalgGen . Left $ sk) (m ! t)) m) ret $ Map.toList $ csks col
   ret   = Map.fromSet (const Set.empty) $ ctys col

-- | Inlines type-algebra equations of the form @gen = term@.
-- The hard work is delegtated to functions from the Term module.
simplifyAlg
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk, x, y])
  => Algebra var ty sym en fk att gen sk x y
  -> Algebra var ty sym en fk att gen sk x y
simplifyAlg
  (Algebra sch en' nf''' nf'''2 repr''' ty'  nf''''  repr'''' teqs'   ) =
   Algebra sch en' nf''' nf'''2 repr''' ty'' nf''''' repr'''' teqs''''
   where
    teqs''       = Set.map (\x -> (Map.empty, x)) teqs'
    (teqs''', f) = simplifyFix teqs'' []
    teqs''''     = Set.map snd teqs'''
    ty'' t       = Set.filter (\x -> not $ elem (HSk x) $ fst $ unzip f) $ ty' t
    nf''''' e    = replaceRepeatedly f $ nf'''' e

instance NFData InstanceEx where
  rnf (InstanceEx x) = rnf x

instance (NFData en, NFData fk, NFData att, NFData gen, NFData sk) => NFData (TalgGen en fk att gen sk) where
  rnf (MkTalgGen x) = rnf x

instance (Show en, Show fk, Show att, Show gen, Show sk) => Show (TalgGen en fk att gen sk) where
  show (MkTalgGen (Left  x)) = show x
  show (MkTalgGen (Right x)) = show x

deriving instance (Ord en, Ord fk, Ord att, Ord gen, Ord sk) => Ord (TalgGen en fk att gen sk)

deriving instance (Eq fk, Eq att, Eq gen, Eq sk) => Eq (TalgGen en fk att gen sk)

assembleGens :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
 => Collage var ty sym en fk att gen sk -> [Carrier en fk gen] -> Map en (Set (Carrier en fk gen))
assembleGens col [] = Map.fromList $ Prelude.map (\x -> (x,Set.empty)) $ Set.toList $ cens col
assembleGens col (e:tl) = Map.insert t (Set.insert e s) m
 where m = assembleGens col tl
       t = typeOf col e
       s = m ! t

close
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var  ty   sym  en fk att  gen sk
  -> (EQ     var  ty   sym  en fk att  gen sk    -> Bool)
  -> [Term   Void Void Void en fk Void gen Void]
close col dp' =
  y (close1m dp' col) $ fmap Gen $ Map.keys $ cgens col
  where
    y f x = let z = f x in if x == z then x else y f z

close1m
  :: (Foldable t, ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
  => (EQ var ty sym en fk att gen sk -> Bool)
  -> Collage var ty sym en fk att gen sk
  -> t (Term Void Void Void en fk Void gen Void)
  -> [Term Void Void Void en fk Void gen Void]
close1m dp' col = dedup dp' . concatMap (close1 col dp')

dedup :: (EQ var ty sym en fk att gen sk -> Bool)
               -> [Term Void Void Void en fk Void gen Void]
               -> [Term Void Void Void en fk Void gen Void]
dedup dp' = nubBy (\x y -> dp' (EQ (upp x, upp y)))

close1 :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
 => Collage var ty sym en fk att gen sk -> (EQ var ty sym en fk att gen sk -> Bool) -> Term Void Void Void en fk Void gen Void -> [ (Term Void Void Void en fk Void gen Void) ]
close1 col _ e = e:(fmap (\(x,_) -> Fk x e) l)
  where t = typeOf col e
        l = fksFrom col t


--------------------------------------------------------------------------------------------------------
-- Instance syntax

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

instance Deps InstanceExp where
  deps x = case x of
    InstanceVar v                       -> [(v, INSTANCE)]
    InstanceInitial  t                  -> deps t
    InstanceDelta  f i _                -> (deps f) ++ (deps i)
    InstanceSigma  f i _                -> (deps f) ++ (deps i)
    InstancePi     f i                  -> (deps f) ++ (deps i)
    InstanceEval   q i                  -> (deps q) ++ (deps i)
    InstanceCoEval q i                  -> (deps q) ++ (deps i)
    InstanceRaw (InstExpRaw' s _ _ _ i) -> (deps s) ++ (concatMap deps i)

getOptionsInstance :: InstanceExp -> [(String, String)]
getOptionsInstance x = case x of
  InstanceVar _                       -> []
  InstanceInitial _                   -> []
  InstanceDelta  _ _ o                -> o
  InstanceSigma  _ _ o                -> o
  InstancePi     _ _                  -> undefined
  InstanceEval   _ _                  -> undefined
  InstanceCoEval _ _                  -> undefined
  InstanceRaw (InstExpRaw' _ _ _ o _) -> o


----------------------------------------------------------------------------------------------------------------------
-- Literal instances

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
  :: forall var ty sym en fk att . (Ord ty, Ord sym, Ord en, Ord fk, Ord att, Typeable ty, Typeable sym, Typeable en, Typeable fk, Typeable att)
  => Schema var ty sym en fk att
  -> InstExpRaw'
  -> [Presentation var ty sym en fk att Gen Sk]
  -> Err (Presentation var ty sym en fk att Gen Sk)
evalInstanceRaw' sch (InstExpRaw' _ gens0 eqs' _ _) is = do
  (gens', sks') <- split'' (Set.toList $ Schema.ens sch) (Set.toList $ tys $ typeside sch) gens0
  gens''        <- toMapSafely gens'
  gens'''       <- return $ Map.toList gens''
  sks''         <- toMapSafely sks'
  sks'''        <- return $ Map.toList sks''
  let gensX = concatMap (Map.toList . gens) is ++ gens'''
      sksX  = concatMap (Map.toList . sks ) is ++ sks'''
  eqs'' <- transEq gensX sksX eqs'
  pure $ Presentation (Map.fromList gensX) (Map.fromList sksX) $ Set.fromList $ (concatMap (Set.toList . eqs0) is) ++ (Set.toList eqs'')
  where
    keys' = fst . unzip

    transEq _ _ [] = pure $ Set.empty
    transEq gens' sks' ((lhs, rhs):eqs'') = do
      lhs' <- transTerm (keys' gens') (keys' sks') lhs
      rhs' <- transTerm (keys' gens') (keys' sks') rhs
      rest <- transEq gens' sks' eqs''
      pure $ Set.insert (EQ (lhs', rhs')) rest

    --transPath :: forall en fk gen . [String] -> RawTerm -> Err (Term Void Void Void en fk Void Gen Void)
    transPath gens' (RawApp x [])     | elem  x gens' = pure $ Gen x
    transPath gens' (RawApp x (a:[])) | elem' x (Map.keys $ sch_fks sch) = Fk (fromJust $ cast x) <$> transPath gens' a
    transPath _ x = Left $ "cannot type " ++ show x

    --transTerm :: forall ty sym en fk att Gen Sk . [String] -> [String] -> RawTerm -> Err (Term Void ty sym en fk att Gen Sk)
    transTerm gens' _    (RawApp x [])     | elem  x gens' = pure $ Gen x
    transTerm _     sks' (RawApp x [])     | elem  x sks'  = pure $ Sk  x
    transTerm gens' _    (RawApp x (a:[])) | elem' x (Map.keys $ sch_fks  sch) = Fk  (fromJust $ cast x) <$> transPath gens' a
    transTerm gens' _    (RawApp x (a:[])) | elem' x (Map.keys $ sch_atts sch) = Att (fromJust $ cast x) <$> transPath gens' a
    transTerm gens' sks' (RawApp v l) = case cast v :: Maybe sym of
        Just x -> Sym x <$> mapM (transTerm gens' sks') l
        Nothing -> Left $ "Cannot type: " ++ v

evalInstanceRaw
  :: (ShowOrdTypeableN '[var, ty, sym, en, fk, att])
  => Options
  -> Schema var ty sym en fk att
  -> InstExpRaw'
  -> [InstanceEx]
  -> Err InstanceEx
evalInstanceRaw ops ty' t is =
 do (i :: [Presentation var ty sym en fk att Gen Sk]) <- doImports is
    r <- evalInstanceRaw' ty' t i
    _ <- typecheckPresentation ty' r
    l <- toOptions ops $ instraw_options t
    if bOps l Interpret_As_Algebra
    then do
      j <- saturatedInstance ty' r
      pure $ InstanceEx j
    else do
      p <- createProver (presToCol ty' r) l
      pure $ InstanceEx $ initialInstance r (prv p) ty'
 where
    prv p (EQ (l,r)) = prove p (Map.fromList []) (EQ (l,  r))
    doImports [] = return []
    doImports ((InstanceEx ts):r) = case cast (pres ts) of
      Nothing  -> Left "Bad import"
      Just ts' -> do { r' <- doImports r ; return $ ts' : r' }

---------------------------------------------------------------------------------------------------------------
-- Basic instances

-- | The empty (instance) on a schema has no data, so the type sof its generators and carriers are Void.
emptyInstance :: Schema var ty sym en fk att -> Instance var ty sym en fk att Void Void Void Void
emptyInstance ts'' = Instance ts''
    (Presentation Map.empty Map.empty Set.empty)
    (const undefined)
    (Algebra ts''
      (const Set.empty) (const undefined) (const undefined) (const undefined)
      (const Set.empty) (const undefined) (const undefined)
      Set.empty)

pivot :: forall var ty sym en fk att gen sk x y
  . (ShowOrdTypeableN '[var, ty, sym, en, fk, att, gen, sk, x, y])
  => Instance  var ty sym     en      fk      att  gen sk x   y
  -> (Schema   var ty sym (x, en) (x, fk) (x, att)
  ,   Instance var ty sym (x, en) (x, fk) (x, att) (x, en) y (x, en)  y
  ,   Mapping  var ty sym (x, en) (x, fk) (x, att)     en  fk att)
pivot (Instance sch (Presentation _ sks _) idp (Algebra _ ens gens'' fk fn tys nnf rep2'' teqs)) = (sch', inst, mapp)
  where
    sch'_ens  = Set.fromList [  (x, en)                                | en <- Set.toList (Schema.ens sch), x <- Set.toList (ens en)]
    sch'_fks  = Map.fromList [ ((x, fk0 ), ((x, en), (fk fk0 x, en'))) | en <- Set.toList (Schema.ens sch), x <- Set.toList (ens en), (fk0,  en') <- fksFrom'  sch en ]
    sch'_atts = Map.fromList [ ((x, att0), ((x, en),  ty'           )) | en <- Set.toList (Schema.ens sch), x <- Set.toList (ens en), (att0, ty') <- attsFrom' sch en ]
    sch'_peqs = Set.empty
    sch'_oeqs = Set.empty
    dp' :: EQ Void ty sym (x, en) (x, fk) (x, att) (x, en) y -> Bool
    dp' (EQ (l, r)) = idp $ EQ (instToInst l, instToInst r)
    ens' = Set.singleton
    gen'  = id
    fk' (x, f) (x', en) | x == x' = (fk f x', snd $ Schema.sch_fks sch ! f)
                        | otherwise = error "anomaly, please report"
    rep'  = Gen
    nnf' (Left sk) = Sk sk
    nnf' (Right ((x, en), (x', att))) | x == x' = nnf $ Right (x', att)
                                      | otherwise = error "anomaly, please report"
    rep2' = Sk
    gens' = Map.fromList [ ((x, en), (x, en))   | en <- Set.toList (Schema.ens sch),              x <- Set.toList (ens en) ]
    sks'  = Map.fromList [ ( y, ty)             | ty <- Set.toList (Typeside.tys $ typeside sch), y <- Set.toList (tys ty) ]
    eqs'  = undefined
    es'   = teqs
    tys'  = tys
    em    = Map.fromList [ ((x, en)  , en)               | en <- Set.toList (Schema.ens sch), x <- Set.toList (ens en) ]
    fm    = Map.fromList [ ((x, fk ) , Fk  fk  $ Var ()) | (x, fk ) <- Map.keys sch'_fks  ]
    am    = Map.fromList [ ((x, att) , Att att $ Var ()) | (x, att) <- Map.keys sch'_atts ]

    dp2 :: (x, en) -> EQ () ty sym (x, en) (x, fk) (x, att) Void Void -> Bool
    dp2 (x, en) (EQ (l, r)) = idp $ EQ (schToInst' x l, schToInst' x r)

    sch'  = Schema (typeside sch) sch'_ens sch'_fks sch'_atts sch'_peqs sch'_oeqs dp2
    inst  = Instance sch' (Presentation gens' sks' eqs') dp' $ Algebra sch' ens' gen' fk' rep' tys' nnf' rep2' es'
    mapp  = Mapping sch' sch em fm am

    schToInst' :: x -> Term () ty sym (x, en) (x, fk) (x, att) Void Void -> Term Void ty sym en fk att gen sk
    schToInst' x z = case z of
      Sym f as -> Sym f $ fmap (schToInst' x) as
      Att (x', f) a -> Att f $ schToInst' x a
      Sk x0 -> absurd x0
      Var () -> upp $ fn x
      Fk (x', f) a -> Fk f $ schToInst' x a
      Gen x0 ->  absurd x0

    instToInst :: Term Void ty sym (x, en) (x, fk) (x, att) (x, en) y -> Term Void ty sym en fk att gen sk
    instToInst z = case z of
      Sym f as -> Sym f $ fmap instToInst as
      Att (x', f) a -> Att f $ instToInst a
      Sk y -> rep2'' y
      Var x -> absurd x
      Fk (x', f) a -> Fk f $ instToInst a
      Gen (x, _) -> upp $ fn x

-- coproducts, etc

---------------------------------------------------------------------------------------------------------------
-- Functorial data migration

subs
  :: (Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord en', Ord fk', Ord att', Ord gen, Ord sk)
  => Mapping var ty sym en fk att en' fk' att'
  -> Presentation var ty sym en  fk  att  gen sk
  -> Presentation var ty sym en' fk' att' gen sk
subs (Mapping _ _ ens' fks' atts') (Presentation gens' sks' eqs') = Presentation gens'' sks' eqs''
  where
    gens'' = Map.map (\k -> ens' ! k) gens'
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
  Fk  h a  -> subst (upp $ fks'  ! h) $ changeEn fks' atts' a
  Att h a  -> subst (upp $ atts' ! h) $ changeEn fks' atts' a

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
  Fk h a  -> subst (upp $ fks' ! h) $ changeEn' fks' atts' a
  Att h _ -> absurd h

evalSigmaInst
  :: (ShowOrdN '[var, ty, sym, en', fk', att', gen, sk], Ord en, Ord fk, Ord att, Typeable var, Typeable ty, Typeable sym, Typeable en', Typeable fk', Typeable att', Typeable gen, Typeable sk )
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en fk att gen sk x y -> Options
  -> Err (Instance var ty sym en' fk' att' gen sk (Carrier en' fk' gen) (TalgGen en' fk' att' gen sk))
evalSigmaInst f i o = do
  d <- createProver (presToCol s p) o
  return $ initialInstance p (\(EQ (l, r)) -> prove d Map.empty (EQ (l, r))) s
  where
    p = subs f $ pres i
    s = dst  f

mapGen :: (t1 -> t2) -> Term var ty sym en (t2 -> t2) att t1 sk -> t2
mapGen f (Gen g)   = f g
mapGen f (Fk fk a) = fk $ mapGen f a
mapGen _ _         = error "please report, error on mapGen"

evalDeltaAlgebra
  :: forall var ty sym en fk att gen sk x y en' fk' att'
   . (Ord en, Ord fk, Ord att, Ord x)
  => Mapping  var ty sym en  fk  att  en'       fk' att'
  -> Instance var ty sym en' fk' att' gen       sk  x       y
  -> Algebra  var ty sym en  fk  att  (en, x)   y   (en, x) y
evalDeltaAlgebra (Mapping src' _ ens' fks0 atts0)
  (Instance _ _ _ (alg@(Algebra _ en' _ _ repr''' ty' _ _ teqs')))
  = Algebra src' en'' nf''x1 nf''x2 Gen ty' nf'''' Sk teqs'
 where
  en'' e = Set.map (\x -> (e,x)) $ en' $ ens' ! e

  --nf''x :: Term Void Void Void en fk Void (en, x) Void -> (en, x)
  --nf''x (Gen g) = g
  --nf''x (Fk f a) = (snd $ Schema.fks src' ! f, nf''' $ subst (upp $ fks0 ! f) (repr''' $ snd $ nf''x a))
  --nf''x _ = error "please report, error in eval delta"

  nf''x1 g = g
  nf''x2 f a =  (snd $ Schema.fks src' ! f, nf alg $ subst (upp $ fks0 ! f) (repr''' $ snd $ a))
  nf'''' :: y + ((en,x), att) -> Term Void ty sym Void Void Void Void y
  nf'''' (Left y) = Sk y
  nf'''' (Right ((_, x), att)) = nf'' alg $ subst (upp $ atts0 ! att) (upp $ repr''' x)


evalDeltaInst
  :: forall var ty sym en fk att gen sk x y en' fk' att'
  . (Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord x, Ord y, Ord var,
     Show var, Show ty, Show sym, Show en, Show fk, Show att, Show x, Show y,
     NFData var, NFData ty, NFData sym, NFData en, NFData fk, NFData att, NFData x, NFData y)
  => Mapping var ty sym en fk att en' fk' att'
  -> Instance var ty sym en' fk' att' gen sk x y -> Options
  -> Err (Instance var ty sym en fk att (en,x) y (en,x) y)
evalDeltaInst m i _ = pure $ Instance (src m) (algebraToPresentation alg) eq' alg
  where
    alg = evalDeltaAlgebra m i
    eq' (EQ (l, r)) = dp i $ EQ (translateTerm l, translateTerm r)

    --translateTerm :: Term Void ty sym en  fk  att (en, x) y -> Term Void ty sym en' fk' att' gen    sk
    translateTerm t = case t of
      Var v      -> absurd v
      Sym s'  as -> Sym s' $ translateTerm <$> as
      Fk  fk  a  -> subst (upp $ Mapping.fks  m ! fk ) $ translateTerm a
      Att att a  -> subst (upp $ Mapping.atts m ! att) $ translateTerm a
      Gen (_, x) -> upp  $ repr  (algebra i) x
      Sk  y      ->        repr' (algebra i) y


-------------------------------------------------------------------------------------------------------------------
-- Printing

deriving instance Show (InstanceEx)

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Eq en, Eq fk, Eq att)
  => Show (Instance var ty sym en fk att gen sk x y) where
  show (Instance _ p _ alg) =
    "instance\n" ++
    show p ++ "\n" ++
    show alg

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Eq en, Eq fk, Eq att)
  => Show (Algebra var ty sym en fk att gen sk x y) where
  show alg@(Algebra sch _ _ _ _ ty' _ _ teqs') =
    "algebra" ++ "\n" ++
    (intercalate "\n\n" prettyEntities) ++ "\n" ++
    "type-algebra" ++ "\n" ++
    "nulls" ++ "\n" ++
    w ++
    prettyTypeEqns
    where
      w = "  " ++ (intercalate "\n  " . mapl w2 . Typeside.tys . Schema.typeside $ sch)
      w2 ty'' = show ty'' ++ " (" ++ (show . Set.size $ ty' ty'') ++ ") = " ++ show (Foldable.toList $ ty' ty'') ++ " "
      prettyEntities = prettyEntityTable alg `mapl` Schema.ens sch
      prettyTypeEqns = intercalate "\n" (Set.map show teqs')

prettyEntity
  :: (Show ty, Show sym, Show en, Show fk, Show att, Show x, Show y, Eq en)
  => Algebra var ty sym en fk att gen sk x y
  -> en
  -> String
prettyEntity alg@(Algebra sch en' _ _ _ _ _ _ _) es =
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
  :: (Show ty, Show sym, Show en, Show fk, Show att, Show x, Show y, Eq en)
  => Algebra var ty sym en fk att gen sk x y
  -> en
  -> String
prettyEntityTable alg@(Algebra sch en' _ _ _ _ _ _ _) es =
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
      (prettyTypedIdent <$> fksFrom'  sch es) ++
      (prettyTypedIdent <$> attsFrom' sch es)

    prettyRow e =
      (prettyFk e <$> fksFrom' sch es) ++ (prettyAtt e <$> attsFrom' sch es)

    prettyTypedIdent (ident, typ) = show ident ++ " : " ++ show typ

    prettyFk x (fk, _) = show $ aFk alg fk x

    -- prettyAtt :: x -> (att, w) -> String
    prettyAtt x (att,_) = prettyTerm $ aAtt alg att x

    prettyTerm = show

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk)
  => Show (Presentation var ty sym en fk att gen sk) where
  show (Presentation ens' _ eqs') = "presentation {\n" ++
    "generators\n\t" ++ showCtx' ens' ++ "\n" ++
    "equations\n\t" ++ intercalate "\n\t" (Set.map show eqs') ++ "}"

