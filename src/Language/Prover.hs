{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitForAll        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImpredicativeTypes    #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.Prover where
import           Data.List
import           Data.Map
import           Data.Maybe
import           Data.Rewriting.CriticalPair as CP
import           Data.Rewriting.Rule         as R
import           Data.Rewriting.Rules        as Rs
import           Data.Rewriting.Term         as T
import           Data.Set                    as Set
import           Language.Common
import           Language.Options            as O hiding (Prover)
import           Language.Term               as S
import           Prelude                     hiding (EQ)
import           Twee                        as Twee
import           Twee.Base                   as TweeBase
import           Twee.Equation               as TweeEq
import qualified Twee.KBO                    as KBO
import           Twee.Proof                  as TweeProof hiding (defaultConfig)
--import Debug.Trace
import           Data.Map.Strict             as Map
import           Data.Typeable
import           Language.Congruence         as Cong
import           Language.Internal           (Term)



-- Theorem proving ------------------------------------------------

data ProverName = Free | Congruence | Orthogonal | Completion | Auto
  deriving Show

proverStringToName :: Options -> Err ProverName
proverStringToName m = case sOps m prover_name of
  "auto"       -> pure Auto
  "completion" -> pure Completion
  "program"    -> pure Orthogonal
  "congruence" -> pure Congruence
  x            -> Left $ "Not a prover: " ++ x

-- | A decision procedure for equality of terms in a collage.
data Prover var ty sym en fk att gen sk = Prover
  { collage :: Collage var ty sym en fk att gen sk
  , prove   :: Ctx var (ty+en) -> EQ var ty sym en fk att gen sk -> Bool
  }

-- | Create a prover from a collage and user-provided options.
createProver
  :: (ShowOrdTypeableNFDataN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Options
  -> Err (Prover var  ty  sym  en  fk  att  gen  sk)
createProver col ops = do
  p <- proverStringToName ops
  case p of
    Free       -> freeProver col
    Orthogonal -> orthProver col ops
    Auto       -> if Set.null (ceqs col)
      then if eqsAreGround col
           then congProver col
           else orthProver col ops
      else orthProver col ops
    Completion -> kbProver col ops
    Congruence -> congProver col

-------------------------------------------------------------------------------------------

-- | For theories with no equations, syntactic equality works.
freeProver
  :: TyMap Eq '[var, sym, fk, att, gen, sk]
  => Collage var ty sym en fk att gen sk
  -> Either String (Prover var ty sym en fk att gen sk)
freeProver col | Set.size (ceqs col) == 0 = return $ Prover col p
               | otherwise = Left "Cannot use free prover when there are equations"
  where
    p _ (EQ (lhs', rhs')) = lhs' == rhs'

-------------------------------------------------------------------------------------------

-- | A prover for weakly orthogonal theories: http://hackage.haskell.org/package/term-rewriting.
-- We must have size reducing equations of the form lhs -> rhs
-- without empty sorts and without non-trivial critical pairs (rule overlaps).
-- Runs the rules non deterministically to get a unique normal form.
orthProver
  :: (ShowOrdNFDataN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Options
  -> Err (Prover var ty sym en fk att gen sk)
orthProver col ops = if isDecreasing eqs1 || allow_nonTerm
  then     if nonConOk || noOverlaps  eqs2
    then   if allSortsInhabited col  || allow_empty
      then let p' ctx (EQ (l, r)) = p ctx $ EQ (replaceRepeatedly f l, replaceRepeatedly f r)
           in pure $ Prover col p'
      else Left   "Rewriting Error: contains uninhabited sorts"
    else   Left $ "Rewriting Error: not orthogonal.  Pairs are " ++ show (findCps eqs2)
  else     Left   "Rewriting Error: not size decreasing"
  where
    (col', f) = simplifyCol col

    p _ (EQ (lhs', rhs')) = nf (convert' lhs') == nf (convert' rhs')

    eqs1 = Prelude.map snd $ Set.toList $ ceqs col'
    eqs2 = Prelude.map convert'' eqs1

    nf x = case outerRewrite eqs2 x of
      []  -> x
      y:_ -> nf $ result y

    allow_nonTerm =  bOps ops Program_Allow_Nontermination_Unsafe
    allow_empty   =  bOps ops Allow_Empty_Sorts_Unsafe
    nonConOk      =  bOps ops Program_Allow_Nonconfluence_Unsafe
    convert'' (EQ (lhs', rhs')) = Rule (convert' lhs') (convert' rhs')

    -- | Gets the non-reflexive critical pairs
    findCps :: (Eq f, Ord v') => [Rule f v'] -> [(R.Term f (Either v' v'), R.Term f (Either v' v'))]
    findCps x = Prelude.map (\y -> (CP.left y, CP.right y)) $ Prelude.filter g $ cps' x
      where
        g q = not $ (CP.left q) == (CP.right q)

    noOverlaps :: (Ord v, Eq f) => [Rule f v] -> Bool
    noOverlaps x = (and $ Prelude.map R.isLeftLinear x) && (Prelude.null $ findCps x)

    isDecreasing :: Eq var => [EQ var ty sym en fk att gen sk] -> Bool
    isDecreasing [] = True
    isDecreasing (EQ (lhs', rhs') : tl) = S.size lhs' > S.size rhs' && isDecreasing tl && moreOnLhs (S.vars lhs') (S.vars rhs')
      where
        moreOnLhs lvars rvars = and $ fmap (\r -> count lvars r >= count rvars r) rvars
        count [] _    = 0
        count (a:b) x = count b x + if a == x then 1 else 0 :: Integer

    convert' :: S.Term var ty sym en fk att gen sk -> T.Term (Head ty sym en fk att gen sk) var
    convert' x = case x of
      S.Var v    -> T.Var v
      S.Gen g    -> T.Fun (HGen g) []
      S.Sk  g    -> T.Fun (HSk  g) []
      S.Att g a  -> T.Fun (HAtt g) [convert' a]
      S.Fk  g a  -> T.Fun (HFk  g) [convert' a]
      S.Sym g as -> T.Fun (HSym g) $ Prelude.map convert' as

----------------------------------------------------------------------------------------------
-- for arbitrary theories: http://hackage.haskell.org/package/twee

data Constant x = Constant
  { con_prec  :: !Precedence
  , con_id    :: !x
  , con_arity :: !Int
  , con_size  :: !Int
  , con_bonus :: !(Maybe (Maybe Bool))
  } deriving (Eq, Ord)

instance Sized (Constant x) where
  size (Constant _ _ _ y _) = y

instance Arity (Constant x) where
  arity (Constant _ _ y _ _) = y

instance Show x => Pretty (Constant x) where
  pPrint (Constant _ y _ _ _) = text $ show y

instance Show x => PrettyTerm (Constant x) where

instance (Show x, Ord x, Typeable x) => Ordered (Extended (Constant x)) where
  lessEq t u = KBO.lessEq t u
  lessIn model t u = KBO.lessIn model t u

instance EqualsBonus (Constant x) where
  hasEqualsBonus = isJust . con_bonus
  isEquals = not . isJust . fromJust . con_bonus
  isTrue = fromJust . fromJust . con_bonus
  isFalse = fromJust . fromJust . con_bonus

data Precedence = Precedence !Bool !(Maybe Int) !Int
  deriving (Eq, Ord)

prec
  :: (ShowOrdTypeableNFDataN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Head        ty sym en fk att gen sk
  -> Precedence
prec col c = Precedence p q r -- trace (show (p,q,r)) $
  where
    prec' = [] --[show "I", show "o", show "e"] -- for now
    p = isNothing $ elemIndex (show c) prec'
    q = fmap negate (elemIndex (show c) prec')
    r = negate (Map.findWithDefault 0 c $ occs col)

toTweeConst
  :: (ShowOrdTypeableNFDataN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Head        ty sym en fk att gen sk
  -> Constant (Head ty sym en fk att gen sk)
toTweeConst col c = Constant (prec col c) c arr sz Nothing
  where
    sz = 1 -- for now
    arr = case c of
      HGen _ -> 0
      HSk  _ -> 0
      HAtt _ -> 1
      HFk  _ -> 1
      HSym s -> length $ fst $ (csyms col) ! s

convert
  :: (ShowOrdTypeableNFDataN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Ctx var (ty+en)
  -> S.Term var ty sym en fk att gen sk
  -> TweeBase.Term (Extended (Constant (Head ty sym en fk att gen sk)))
convert col ctx x = case x of
  S.Var v    -> build $ var $ V (fromJust $ elemIndex v $ keys ctx)
  S.Gen g    -> build $ con (fun $ TweeBase.Function $ toTweeConst col $ HGen g)
  S.Sk  g    -> build $ con (fun $ TweeBase.Function $ toTweeConst col $ HSk  g)
  S.Att g a  -> build $ app (fun $ TweeBase.Function $ toTweeConst col $ HAtt g) [convert col ctx a]
  S.Fk  g a  -> build $ app (fun $ TweeBase.Function $ toTweeConst col $ HFk  g) [convert col ctx a]
  S.Sym g as -> build $ app (fun $ TweeBase.Function $ toTweeConst col $ HSym g) $ fmap (convert col ctx) as

initState
  :: forall                     var  ty  sym  en  fk  att  gen  sk
  .  (ShowOrdTypeableNFDataN '[       var, ty, sym, en, fk, att, gen, sk])
  => Collage                    var  ty  sym  en  fk  att  gen  sk
  -> State (Extended (Constant (Head ty  sym  en  fk  att  gen  sk)))
initState col = Set.foldr (\z s -> addAxiom defaultConfig s (toAxiom z)) initialState $ ceqs col
  where
    toAxiom :: (Ctx var (ty+en), EQ var ty sym en fk att gen sk) -> Axiom (Extended (Constant (Head ty sym en fk att gen sk)))
    toAxiom (ctx, EQ (lhs0, rhs0)) = Axiom 0 "" $ convert col ctx lhs0 :=: convert col ctx rhs0

-- | Does Knuth-Bendix completion.  Attempts to orient equations into rewrite rules
-- lhs -> rhs where the lhs is larger than the rhs, adding additional equations whenever
-- critical pairs (rule overlaps) are detected.
kbProver
  :: forall                     var  ty  sym  en  fk  att  gen  sk
  .  (ShowOrdTypeableNFDataN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Options
  -> Err (Prover var ty sym en fk att gen sk)
kbProver col ops = if allSortsInhabited col || allow_empty
      then let p' ctx (EQ (l, r)) = p ctx $ EQ (replaceRepeatedly f l, replaceRepeatedly f r)
           in pure $ Prover col p'
      else Left "Completion Error: contains uninhabited sorts"
  where
    (col', f) = simplifyCol col
    p ctx (EQ (lhs', rhs')) = normaliseTerm (completed ctx lhs' rhs') (convert col ctx lhs') == normaliseTerm (completed ctx lhs' rhs') (convert col ctx rhs')
    completed g l r = completePure defaultConfig $ addGoal defaultConfig (initState col') (toGoal g l r)
    allow_empty = bOps ops Allow_Empty_Sorts_Unsafe
    toGoal :: Ctx var (ty+en) -> S.Term var ty sym en fk att gen sk -> S.Term var ty sym en fk att gen sk -> Goal (Extended (Constant (Head ty sym en fk att gen sk)))
    toGoal ctx lhs0 rhs0 = goal 0 "" $ convert col ctx lhs0 :=: convert col ctx rhs0

-------------------------------------------------------------------------------------------
-- for ground theories

-- | A Nelson-Oppen style decision procedure for ground (variable-free) theories.  Its unclear
-- how much of the congruence graph gets preserved between calls; the code we have could re-run
-- building the congruence graph on each call to eq.
congProver
  :: (ShowOrdTypeableNFDataN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Err (Prover var ty sym en fk att gen sk)
congProver col = if eqsAreGround col'
  then let prv _ (EQ (l, r)) = doProof (replaceRepeatedly f l) (replaceRepeatedly f r)
           in pure $ Prover col' prv
  else Left   "Congruence Error: Not ground"
  where
    hidden = decide rules'
    rules' = fmap (\(_, EQ (l, r)) -> (convertCong l, convertCong r)) $ Set.toList $ ceqs col
    doProof l r = hidden (convertCong l) (convertCong r)
    (col', f) = simplifyCol col

convertCong
  :: (ShowOrdTypeableNFDataN '[var, ty, sym, en, fk, att, gen, sk])
  => S.Term var ty sym en fk att gen sk
  -> Language.Internal.Term (Head ty sym en fk att gen sk)
convertCong x = case x of
  S.Var _    -> error "Anomaly, please report.  Congruence conversion received variable."
  S.Gen g    -> Cong.Function (HGen g) []
  S.Sk  g    -> Cong.Function (HSk  g) []
  S.Att g a  -> Cong.Function (HAtt g) [convertCong a]
  S.Fk  g a  -> Cong.Function (HFk  g) [convertCong a]
  S.Sym g as -> Cong.Function (HSym g) $ fmap convertCong as


