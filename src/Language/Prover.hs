{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Prover where
import Language.Common
import Language.Term as S
import Data.Set as Set
import Prelude hiding (EQ)
import Data.Rewriting.Term as T
import Data.Rewriting.CriticalPair as CP
import Data.Rewriting.Rule as R
import Data.Rewriting.Rules as Rs
import Language.Options as O hiding (Prover)

-- Theorem proving ------------------------------------------------

data ProverName = Free | Congruence | Orthogonal | KB | Auto
 deriving Show

data Prover var ty sym en fk att gen sk = Prover {
  collage :: Collage var ty sym en fk att gen sk
  , prove :: Ctx var (ty+en) -> EQ var ty sym en fk att gen sk -> Bool
}

proverStringToName :: Options -> Err ProverName
proverStringToName m = case sOps m prover_name of
  "auto" -> pure Auto
  "kb" -> pure KB
  "program" -> pure Orthogonal
  "congruence" -> pure Congruence
  x -> Left $ "Not a prover: " ++ x

freeProver :: (Eq var, Eq sym, Eq fk, Eq att, Eq gen, Eq sk) =>
                    Collage var ty sym en fk att gen sk
                    -> Either String (Prover var ty sym en fk att gen sk)
freeProver col = if (Set.size (ceqs col) == 0)
                 then return $ Prover col p
                 else Left "Cannot use free prover when there are equations"
 where p _ (EQ (lhs', rhs')) = lhs' == rhs'

createProver
  :: (ShowOrd8 var ty sym en fk att gen sk)
  => Collage var ty sym en fk att gen sk
  -> Options
  -> Err (Prover var ty sym en fk att gen sk)
createProver col ops =  do p <- proverStringToName ops
                           case p of
                             Free -> freeProver col
                             Orthogonal -> orthProver col ops
                             Auto -> orthProver col ops
                             z -> Left $ show z ++ " prover not available"


-- for ground theories: https://hackage.haskell.org/package/toysolver-0.0.4/src/src/Algorithm/CongruenceClosure.hs
-- for arbitrary theories: http://hackage.haskell.org/package/twee

-------------------------------------------------------------------------------------------

-- for weakly orthogonal theories: http://hackage.haskell.org/package/term-rewriting

orthProver
  :: (ShowOrd8 var ty sym en fk att gen sk)
  => Collage var ty sym en fk att gen sk
  -> Options
  -> Err (Prover var ty sym en fk att gen sk)
orthProver col ops = if isDecreasing eqs1 || allow_nonTerm
                     then if nonConOk || noOverlaps  eqs2
                          then if allSortsInhabited col  || allow_empty
                            then let p' ctx (EQ (l, r)) = p ctx $ EQ (replaceRepeatedly f l, replaceRepeatedly f r)
                                 in pure $ Prover col p'
                            else Left "Rewriting Error: contains uninhabited sorts"
                          else Left $ "Rewriting Error: not orthogonal.  Pairs are " ++ show (xxx eqs2)
                     else Left "Rewriting Error: not size decreasing"
 where (col', f) = simplifyCol col
       p _ (EQ (lhs', rhs')) = nf (convert lhs') == nf (convert rhs')
       eqs1 = Prelude.map snd $ Set.toList $ ceqs col'
       eqs2 = Prelude.map convert' eqs1
       nf x = case outerRewrite eqs2 x of
              [] -> x
              y:_ -> nf $ result y
       allow_nonTerm =  bOps ops Program_Allow_Nontermination_Unsafe
       allow_empty =  bOps ops Allow_Empty_Sorts_Unsafe
       nonConOk =  bOps ops Program_Allow_Nonconfluence_Unsafe 

convert' :: EQ var ty sym en fk att gen sk -> Rule (Head ty sym en fk att gen sk) var
convert' (EQ (lhs', rhs')) = Rule (convert lhs') (convert rhs')

xxx :: (Eq f, Ord v') =>
             [Rule f v'] -> [(R.Term f (Either v' v'), R.Term f (Either v' v'))]
xxx x = Prelude.map (\y -> (CP.left y, CP.right y)) $ Prelude.filter g $ cps' x
  where g q = not $ (CP.left q) == (CP.right q)

noOverlaps :: (Ord v, Eq f) => [Rule f v] -> Bool
--noOverlaps x = y && (Prelude.null $ trace (show $ cps' x) $ cps' x)
noOverlaps x = y && (Prelude.null $ Prelude.filter g $ cps' x)
 where y = and $ Prelude.map R.isLeftLinear x
       g q = not $ (CP.left q) == (CP.right q)

isDecreasing :: [EQ var ty sym en fk att gen sk] -> Bool
isDecreasing [] = True
isDecreasing (EQ (lhs', rhs') : tl) = S.size lhs' > S.size rhs' && isDecreasing tl

convert :: S.Term var ty sym en fk att gen sk -> T.Term (Head ty sym en fk att gen sk) var
convert (S.Var v) = T.Var v
convert (S.Gen g) = T.Fun (HGen  g) []
convert (S.Sk  g) = T.Fun (HSk g) []
convert (S.Att g a) = T.Fun (HAtt g) [convert a]
convert (S.Fk  g a) = T.Fun (HFk g) [convert a]
convert (S.Sym g as) = T.Fun (HSym g) $ Prelude.map convert as















