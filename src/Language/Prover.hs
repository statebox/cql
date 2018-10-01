{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Prover where
import Language.Common
import Language.Term as S
import Data.Set as Set
import Data.Map.Strict as Map
import Prelude hiding (EQ)
import Data.Rewriting.Term as T
import Data.Rewriting.CriticalPair
import Data.Rewriting.Rule as R
import Data.Rewriting.Rules as Rs
import Debug.Trace
import Language.Options as O hiding (Prover)

-- Theorem proving ------------------------------------------------

data ProverName = Free | Congruence | Orthogonal | KB | Auto

data Prover var ty sym en fk att gen sk = Prover {
  collage :: Collage var ty sym en fk att gen sk
  , prove :: Ctx var (ty+en) -> EQ var ty sym en fk att gen sk -> Bool
}

proverStringToName :: Options -> Err ProverName
proverStringToName m = case Map.lookup prover_name (sOps m) of
 (Just "auto") -> pure Auto
 (Just "kb") -> pure KB
 (Just "program") -> pure Orthogonal
 (Just "congruence") -> pure Congruence
 (Just x) -> Left $ "Not a prover: " ++ x
 Nothing -> pure Auto

freeProver :: (Eq var, Eq sym, Eq fk, Eq att, Eq gen, Eq sk) =>
                    Collage var ty sym en fk att gen sk
                    -> Either String (Prover var ty sym en fk att gen sk)
freeProver col = if (Set.size (ceqs col) == 0)
                 then return $ Prover col p
                 else Left "Cannot use free prover when there are equations"
 where p _ (EQ (lhs, rhs)) = lhs == rhs

createProver ::  (Ord var, Ord ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Ord en, Show en, Show ty)
 => Collage var ty sym en fk att gen sk -> Options 
  -> Err (Prover var ty sym en fk att gen sk)
createProver col ops =  do p <- proverStringToName ops
                           case p of
                             Free -> freeProver col
                             Orthogonal -> orthProver col ops
                             _ -> Left "Prover not available"
 
--todo

-- for ground theories: https://hackage.haskell.org/package/toysolver-0.0.4/src/src/Algorithm/CongruenceClosure.hs
-- for arbitrary theories: http://hackage.haskell.org/package/twee

-------------------------------------------------------------------------------------------

-- for weakly orthogonal theories: http://hackage.haskell.org/package/term-rewriting

orthProver :: (Ord var, Eq sym, Eq fk, Eq att, Eq gen, Eq sk, Ord ty, Ord en, Show en, Show ty) =>
                    Collage var ty sym en fk att gen sk -> Options  
                    -> Err (Prover var ty sym en fk att gen sk)
orthProver col ops = if isDecreasing eqs1 || allow_nonTerm
                     then if noOverlaps  eqs2
                          then if allSortsInhabited col  
	           	               then pure $ Prover col p
	           	    	       else Left "Rewriting Error: contains uninhabited sorts"
	           	          else Left "Rewriting Error: not orthogonal"
	                 else Left "Rewriting Error: not size decreasing"	  
--  | Allow_Empty_Sorts_Unsafe 
 where p _ (EQ (lhs, rhs)) = nf (convert lhs) == nf (convert rhs)
       eqs1 = Prelude.map snd $ Set.toList $ ceqs col
       eqs2 = Prelude.map convert' eqs1
       nf x = case outerRewrite eqs2 x of
       		   [] -> x
       		   y:_ -> nf $ result y 
       allow_nonTerm = lookup2 Program_Allow_Nonterm_Unsafe (bOps ops)	   

convert' :: EQ var ty sym en fk att gen sk -> Rule (Head ty sym en fk att gen sk) var
convert' (EQ (lhs, rhs)) = Rule (convert lhs) (convert rhs)

noOverlaps :: (Ord v, Eq f) => [Rule f v] -> Bool
noOverlaps x = y && (Prelude.null $ cps' x)
 where y = and $ Prelude.map R.isLeftLinear x

isDecreasing [] = True
isDecreasing (EQ (lhs, rhs) : tl) = S.size lhs > S.size rhs && isDecreasing tl

convert :: S.Term var ty sym en fk att gen sk -> T.Term (Head ty sym en fk att gen sk) var 
convert (S.Var v) = T.Var v 
convert (S.Gen g) = T.Fun (Right $ Right $ Right $ Left  g) []
convert (S.Sk  g) = T.Fun (Right $ Right $ Right $ Right g) []
convert (S.Att g a) = T.Fun (Right $ Right $ Left g) [convert $ upTerm a]
convert (S.Fk  g a) = T.Fun (Right $ Left g) [convert $ upTerm a]
convert (S.Sym g as) = T.Fun (Left g) $ Prelude.map convert as















