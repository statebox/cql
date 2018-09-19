{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Prover where
import Language.Common
import Language.Term
import Data.Set as Set
import Data.Map.Strict as Map
import Prelude hiding (EQ)

-- Theorem proving ------------------------------------------------

data ProverName = Free | Congruence | Orthogonal | KB | Auto

data Prover var ty sym en fk att gen sk = Prover {
  collage :: Collage var ty sym en fk att gen sk
  , prove :: Ctx var (Either ty en) -> EQ var ty sym en fk att gen sk
   -> Bool
}


proverStringToName :: Map String String -> Err ProverName
proverStringToName m = case Map.lookup "prover" m of
 (Just "auto") -> pure Auto
 (Just "kb") -> pure KB
 (Just "program") -> pure Orthogonal
 (Just "congruence") -> pure Congruence
 (Just x) -> Left $ "Not a prover: " ++ x
 Nothing -> pure Auto

freeProver :: (Eq var, Eq sym, Eq fk, Eq att, Eq gen, Eq sk) =>
                    Collage var ty sym en fk att gen sk
                    -> Either [Char] (Prover var ty sym en fk att gen sk)
freeProver col = if (Set.size (ceqs col) == 0)
                 then return $ Prover col p
                 else Left "Cannot use free prover when there are equations"
 where p _ (EQ (lhs, rhs)) = lhs == rhs

createProver ::  (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk)
 => ProverName -> Collage var ty sym en fk att gen sk
  -> Err (Prover var ty sym en fk att gen sk)
createProver Free col = freeProver col
createProver _ _ = Left "Prover not available"

--todo

-- for ground theories: https://hackage.haskell.org/package/toysolver-0.0.4/src/src/Algorithm/CongruenceClosure.hs
-- for arbitrary theories: http://hackage.haskell.org/package/twee
-- for weakly orthogonal theories: http://hackage.haskell.org/package/term-rewriting

