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
import           Data.Rewriting.CriticalPair as CP
import           Data.Rewriting.Rule         as R
import           Data.Rewriting.Rules        as Rs
import           Data.Rewriting.Term         as T
import           Data.Set                    as Set
import           Language.Common
import           Language.Options            as O hiding (Prover)
import           Language.Term               as S
import           Prelude                     hiding (EQ)
import           Twee.Term                   as TweeTerm
import           Twee.Base                   as TweeBase
import           Twee                        as Twee
import           Data.Maybe
import           Data.Map
import           Data.List
import           Twee.Proof                  as TweeProof hiding (defaultConfig)
import           Twee.Equation               as TweeEq
import qualified Twee.KBO as KBO
import Debug.Trace
import Language.Congruence as Cong
import Language.Internal (Term)


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
  , prove :: Ctx var (ty+en) -> EQ var ty sym en fk att gen sk -> Bool
  }

-- | Create a prover from a collage and user-provided options.
createProver
  :: (ShowOrdTypeableN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage     var  ty  sym  en  fk  att  gen  sk
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
  :: (Eq var, Eq sym, Eq fk, Eq att, Eq gen, Eq sk)
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
  :: (ShowOrdN '[var, ty, sym, en, fk, att, gen, sk])
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

    p _ (EQ (lhs', rhs')) = nf (convert lhs') == nf (convert rhs')

    eqs1 = Prelude.map snd $ Set.toList $ ceqs col'
    eqs2 = Prelude.map convert' eqs1

    nf x = case outerRewrite eqs2 x of
      []  -> x
      y:_ -> nf $ result y

    allow_nonTerm =  bOps ops Program_Allow_Nontermination_Unsafe
    allow_empty   =  bOps ops Allow_Empty_Sorts_Unsafe
    nonConOk      =  bOps ops Program_Allow_Nonconfluence_Unsafe
    convert' (EQ (lhs', rhs')) = Rule (convert lhs') (convert rhs')

    -- | Gets the non-reflexive critical pairs
    findCps :: (Eq f, Ord v') => [Rule f v'] -> [(R.Term f (Either v' v'), R.Term f (Either v' v'))]
    findCps x = Prelude.map (\y -> (CP.left y, CP.right y)) $ Prelude.filter g $ cps' x
      where
        g q = not $ (CP.left q) == (CP.right q)

    noOverlaps :: (Ord v, Eq f) => [Rule f v] -> Bool
    noOverlaps x = (and $ Prelude.map R.isLeftLinear x) && (Prelude.null $ findCps x)

    isDecreasing :: [EQ var ty sym en fk att gen sk] -> Bool
    isDecreasing [] = True
    isDecreasing (EQ (lhs', rhs') : tl) = S.size lhs' > S.size rhs' && isDecreasing tl

    convert :: S.Term var ty sym en fk att gen sk -> T.Term (Head ty sym en fk att gen sk) var
    convert x = case x of
      S.Var v    -> T.Var v
      S.Gen g    -> T.Fun (HGen g) []
      S.Sk  g    -> T.Fun (HSk  g) []
      S.Att g a  -> T.Fun (HAtt g) [convert a]
      S.Fk  g a  -> T.Fun (HFk  g) [convert a]
      S.Sym g as -> T.Fun (HSym g) $ Prelude.map convert as

----------------------------------------------------------------------------------------------
-- for arbitrary theories: http://hackage.haskell.org/package/twee

instance (ShowOrdTypeableN '[ty, sym, en, fk, att, gen, sk])
  => Ordered (Extended (Head ty (sym, Int) en fk att gen sk)) where
  lessEq = KBO.lessEq
  lessIn = KBO.lessIn

instance Arity (Head ty (sym, Int) en fk att gen sk) where
  arity x = case x of
    HGen _ -> 0
    HSk _ -> 0
    HAtt _ -> 1
    HFk _ -> 1
    HSym (_, i) -> i

instance (ShowOrdTypeableN '[ty, sym, en, fk, att, gen, sk]) =>
  PrettyTerm (Head ty (sym, Int) en fk att gen sk) where

instance EqualsBonus (Head ty (sym, Int) en fk att gen sk) where

instance Sized (Head ty (sym, Int) en fk att gen sk) where
  size x = case x of
    HGen _ -> 1
    HSk _ -> 1
    HAtt _ -> 1
    HFk _ -> 1
    HSym (_, i) -> 1

instance (Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk)
  => Pretty (Head ty (sym, Int) en fk att gen sk) where
  pPrint x = text $ show x

convert
  :: (ShowOrdTypeableN '[var, ty, sym, en, fk, att, gen, sk])
  => Ctx var (ty+en)
  -> S.Term var ty sym en fk att gen sk
  -> TweeBase.Term (Extended (Head ty (sym, Int) en fk att gen sk))
convert ctx x = case x of
  S.Var v    -> build $ var $ V (fromJust $ elemIndex v $ keys ctx)
  S.Gen g    -> build $ con (fun $ TweeBase.Function $ HGen g)
  S.Sk  g    -> build $ con (fun $ TweeBase.Function $ HSk  g)
  S.Att g a  -> build $ app (fun $ TweeBase.Function $ HAtt g) [convert ctx a]
  S.Fk  g a  -> build $ app (fun $ TweeBase.Function $ HFk  g) [convert ctx a]
  S.Sym g as -> build $ app (fun $ TweeBase.Function $ HSym (g, length as)) $ fmap (convert ctx) as

initState
  :: forall              var  ty  sym         en  fk  att  gen  sk
  .  (ShowOrdTypeableN '[var, ty, sym,        en, fk, att, gen, sk])
  => Collage             var  ty  sym         en  fk  att  gen  sk
  -> State (Extended (Head    ty (sym, Int)   en  fk  att  gen  sk))
initState col = Set.foldr (\z s -> addAxiom defaultConfig s (toAxiom z)) initialState $ ceqs col
  where
    toAxiom :: (Ctx var (ty+en), EQ var ty sym en fk att gen sk) -> Axiom (Extended (Head ty (sym, Int) en fk att gen sk))
    toAxiom (ctx, EQ (lhs, rhs)) = Axiom 0 "" $ (convert ctx lhs) :=: convert ctx rhs

-- | Does Knuth-Bendix completion.  Attempts to orient equations into rewrite rules
-- lhs -> rhs where the lhs is larger than the rhs, adding additional equations whenever
-- critical pairs (rule overlaps) are detected.
kbProver
  :: (ShowOrdTypeableN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Options
  -> Err (Prover var ty sym en fk att gen sk)
kbProver col ops = if allSortsInhabited col || allow_empty
      then let p' ctx (EQ (l, r)) = p ctx $ EQ (replaceRepeatedly f l, replaceRepeatedly f r)
           in trace (show $ rules $ completed) $ pure $ Prover col p'
      else Left "Completion Error: contains uninhabited sorts"
  where
    (col', f) = simplifyCol col
    p ctx (EQ (lhs', rhs')) = normaliseTerm completed (convert ctx lhs') == normaliseTerm completed (convert ctx rhs')
    completed = completePure defaultConfig (initState col')
    allow_empty = bOps ops Allow_Empty_Sorts_Unsafe

-------------------------------------------------------------------------------------------
-- for ground theories

-- | A Nelson-Oppen style decision procedure for ground (variable-free) theories.  Its unclear
-- how much of the congruence graph gets preserved between calls; the code we have could re-run
-- building the congruence graph on each call to eq.
congProver
  :: (ShowOrdTypeableN '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Err (Prover var ty sym en fk att gen sk)
congProver col = if eqsAreGround col'
  then let prv _ (EQ (l, r)) = doProof (replaceRepeatedly f l) (replaceRepeatedly f r)
           in pure $ Prover col' prv
  else Left   "Congruence Error: Not ground"
  where
    hidden = decide rules
    rules = fmap (\(_, EQ (l, r)) -> (convertCong l, convertCong r)) $ Set.toList $ ceqs col
    doProof l r = hidden (convertCong l) (convertCong r)
    (col', f) = simplifyCol col

convertCong
  :: (ShowOrdTypeableN '[var, ty, sym, en, fk, att, gen, sk])
  => S.Term var ty sym en fk att gen sk
  -> Language.Internal.Term (Head ty sym en fk att gen sk)
convertCong x = case x of
  S.Var v    -> error "Anomaly, please report.  Congruence conversion received variable."
  S.Gen g    -> Cong.Function (HGen g) []
  S.Sk  g    -> Cong.Function (HSk  g) []
  S.Att g a  -> Cong.Function (HAtt g) [convertCong a]
  S.Fk  g a  -> Cong.Function (HFk  g) [convertCong a]
  S.Sym g as -> Cong.Function (HSym g) $ fmap convertCong as


