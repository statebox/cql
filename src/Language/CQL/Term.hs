{-
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `statebox/cql`, the categorical query language.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExplicitForAll        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImpredicativeTypes    #-}
{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.CQL.Term where

import           Control.DeepSeq
import           Data.Map.Merge.Strict
import           Data.Map.Strict       as Map hiding (foldr, size)
import           Data.Maybe
import           Data.Set              as Set hiding (foldr, size)
import           Data.Void
import           Language.CQL.Common
import           Prelude               hiding (EQ)

data RawTerm = RawApp String [RawTerm]
  deriving Eq

instance Show RawTerm where
  show (RawApp sym az) = show sym ++ "(" ++ (intercalate "," . fmap show $ az) ++ ")"

--------------------------------------------------------------------------------------------
-- Terms

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

instance TyMap NFData '[var, ty, sym, en, fk, att, gen, sk] =>
  NFData (Term var ty sym en fk att gen sk) where
    rnf x = case x of
      Var v   -> rnf v
      Sym f a -> let _ = rnf f in rnf a
      Fk  f a -> let _ = rnf f in rnf a
      Att f a -> let _ = rnf f in rnf a
      Gen   a -> rnf a
      Sk    a -> rnf a

instance TyMap NFData '[var, ty, sym, en, fk, att, gen, sk] =>
  NFData (EQ var ty sym en fk att gen sk) where
    rnf (EQ (x, y)) = deepseq x $ rnf y


instance TyMap Show '[var, ty, sym, en, fk, att, gen, sk] =>
  Show (Term var ty sym en fk att gen sk)
  where
    show x = case x of
      Var v      -> show' v
      Gen g      -> show' g
      Sk  s      -> show' s
      Fk  fk  a  -> show' a ++ "." ++ show' fk
      Att att a  -> show' a ++ "." ++ show' att
      Sym sym [] -> show' sym
      Sym sym az -> show' sym ++ "(" ++ (intercalate "," . fmap show' $ az) ++ ")"
      where

show' :: Show a => a -> String
show' = dropQuotes . show

deriving instance TyMap Ord '[var, ty, sym, en, fk, att, gen, sk] => Ord (Term var ty sym en fk att gen sk)

-- | A symbol (non-variable).
data Head ty sym en fk att gen sk
  = HSym  sym
  | HFk   fk
  | HAtt  att
  | HGen  gen
  | HSk   sk
  deriving (Eq, Ord)

instance (Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk)
  => Show (Head ty sym en fk att gen sk) where
  show x = case x of
    HSym  sym -> show' sym
    HFk   fk  -> show' fk
    HAtt  att -> show' att
    HGen  gen -> show' gen
    HSk   sk  -> show' sk

-- | Maps functions through a term.
mapTerm
  :: (var -> var')
  -> (ty  -> ty' )
  -> (sym -> sym')
  -> (en  -> en' )
  -> (fk  -> fk' )
  -> (att -> att')
  -> (gen -> gen')
  -> (sk  -> sk' )
  -> Term var  ty  sym  en  fk  att  gen  sk
  -> Term var' ty' sym' en' fk' att' gen' sk'
mapTerm v t r e f a g s x = case x of
  Var w   -> Var $ v w
  Gen w   -> Gen $ g w
  Sk  w   -> Sk  $ s w
  Fk  w u -> Fk  (f w) $ mt u
  Att w u -> Att (a w) $ mt u
  Sym w u -> Sym (r w) $ fmap mt u
  where
    mt = mapTerm v t r e f a g s

mapVar :: var -> Term () ty sym en fk att gen sk -> Term var ty sym en fk att gen sk
mapVar v = mapTerm (const v) id id id id id id id

-- | The number of variable and symbol occurrences in a term.
size :: Term var ty sym en fk att gen sk -> Integer
size x = case x of
  Var _    -> 1
  Gen _    -> 1
  Sk  _    -> 1
  Att _ a  -> 1 + size a
  Fk  _ a  -> 1 + size a
  Sym _ as -> 1 + foldr (\a y -> size a + y) 0 as

-- | All the variables in a term
vars :: Term var ty sym en fk att gen sk -> [var]
vars x = case x of
  Var v    -> [v]
  Gen _    -> [ ]
  Sk  _    -> [ ]
  Att _ a  -> vars a
  Fk  _ a  -> vars a
  Sym _ as -> concatMap vars as

occsTerm
  :: (Ord sym, Ord fk, Ord att, Ord gen, Ord sk)
  => Term var ty sym en fk att gen sk
  -> Map (Head ty sym en fk att gen sk) Int
occsTerm x = case x of
  Var _    -> Map.empty
  Gen g    -> Map.fromList [(HGen g, 1)]
  Sk  s    -> Map.fromList [(HSk  s, 1)]
  Att f a  -> m (Map.fromList [(HAtt f, 1)]) (occsTerm a)
  Fk  f a  -> m (Map.fromList [(HFk  f, 1)]) (occsTerm a)
  Sym f as -> foldr m (Map.fromList [(HSym f, 1)]) $ fmap occsTerm as
  where
    m = merge preserveMissing preserveMissing $ zipWithMatched (\_ x y -> x + y)

-- | True if sort will be a type.
hasTypeType :: Term Void ty sym en fk att gen sk -> Bool
hasTypeType t = case t of
  Var f   -> absurd f
  Sym _ _ -> True
  Att _ _ -> True
  Sk  _   -> True
  Gen _   -> False
  Fk  _ _ -> False

-- | Assumes variables do not have type type.
hasTypeType'' :: Term var ty sym en fk att gen sk -> Bool
hasTypeType'' t = case t of
  Var _   -> False
  Sym _ _ -> True
  Att _ _ -> True
  Sk  _   -> True
  Gen _   -> False
  Fk  _ _ -> False

----------------------------------------------------------------------------------------------------------
-- Substitution and simplification of theories

-- | Experimental
subst2
  :: forall ty2 sym2 en2 fk2 att2 gen2 sk2 ty3 sym3 en3 fk3 att3 gen3 sk3 var sym en fk att gen sk var3
  . (Eq var,              Up sym2 sym,  Up fk2 fk,  Up att2 att,  Up gen2 gen,  Up sk2 sk,  Up en2 en,
             Up var3 var, Up sym3 sym,  Up fk3 fk,  Up att3 att,  Up gen3 gen,  Up sk3 sk,  Up en3 en,
                          Up sym3 sym2, Up fk3 fk2, Up att3 att2, Up gen3 gen2, Up sk3 sk2, Up en3 en2, Up ty3 ty2)
  => Term ()   ty2 sym2 en2 fk2 att2 gen2 sk2
  -> Term var3 ty3 sym3 en3 fk3 att3 gen3 sk3
  -> Term var  ty2 sym en fk att gen sk
subst2 x t = case x of
  Var ()   -> upp t
  Sym f as -> Sym (upgr f) $ (\a -> subst2 a t) <$> as
  Fk  f a  -> Fk  (upgr f) $ subst2 a t
  Att f a  -> Att (upgr f) $ subst2 a t
  Gen g    -> Gen $ upgr g
  Sk  g    -> Sk  $ upgr g

-- | Given a term with one variable, substitutes the variable with another term.
subst
  :: Eq var
  => Term ()  ty sym en fk att gen sk
  -> Term var ty sym en fk att gen sk
  -> Term var ty sym en fk att gen sk
subst x t = case x of
  Var ()   -> t
  Sym f as -> Sym f $ (`subst` t) <$> as
  Fk  f a  -> Fk  f $ subst a t
  Att f a  -> Att f $ subst a t
  Gen g    -> Gen g
  Sk  g    -> Sk  g

subst'
  :: Term ()   ty   sym  en fk att  Void Void
  -> Term Void Void Void en fk Void gen  Void
  -> Term Void ty   sym  en fk att  gen  sk
subst' s t = case s of
  Var ()   -> upp t
  Sym f as -> Sym f $ (`subst'` t) <$> as
  Fk  f  a -> Fk  f $ subst' a t
  Att f  a -> Att f $ subst' a t
  Gen f    -> absurd f
  Sk  f    -> absurd f


-- | Checks if a given symbol (not variable) occurs in a term.
occurs
  :: (Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk)
  => Head ty sym en fk att gen sk
  -> Term var ty sym en fk att gen sk
  -> Bool
occurs h x = case x of
  Var _     -> False
  Sk  h'    -> h == HSk  h'
  Gen h'    -> h == HGen h'
  Fk  h' a  -> h == HFk  h' || occurs h a
  Att h' a  -> h == HAtt h' || occurs h a
  Sym h' as -> h == HSym h' || any (occurs h) as

-- | If there is one, finds an equation of the form empty |- @gen/sk = term@,
-- where @gen@ does not occur in @term@.
findSimplifiableEqs
  :: (Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk)
  => Theory var ty sym en fk att gen sk
  -> Maybe (Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)
findSimplifiableEqs = procEqs . Set.toList
  where
    g (Var _)    _ = Nothing
    g (Sk  y)    t = if occurs (HSk  y) t then Nothing else Just (HSk  y, t)
    g (Gen y)    t = if occurs (HGen y) t then Nothing else Just (HGen y, t)
    g (Sym _ []) _ = Nothing
    g _ _          = Nothing
    procEqs []  = Nothing
    procEqs ((m, _):tl) | not (Map.null m) = procEqs tl
    procEqs ((_, EQ (lhs, rhs)):tl) = case g lhs rhs of
      Nothing -> case g rhs lhs of
        Nothing -> procEqs tl
        Just y  -> Just y
      Just   y -> Just y

-- | Replaces a symbol by a term in a term.
replace'
  :: (Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk)
  => Head ty sym en fk att gen sk
  -> Term var ty sym en fk att gen sk
  -> Term var ty sym en fk att gen sk
  -> Term var ty sym en fk att gen sk
replace' toReplace replacer x = case x of
  Sk  s    -> if HSk  s == toReplace then replacer else Sk  s
  Gen s    -> if HGen s == toReplace then replacer else Gen s
  Sym f [] -> if HSym f == toReplace then replacer else Sym f []
  Sym f a  -> Sym f $ fmap self a
  Fk  f a  -> Fk  f $ self a
  Att f a  -> Att f $ self a
  Var v    -> Var v
  where
    self = replace' toReplace replacer

replaceRepeatedly
  :: (Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk)
  => [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)]
  -> Term var ty sym en fk att gen sk
  -> Term var ty sym en fk att gen sk
replaceRepeatedly [] t        = t
replaceRepeatedly ((s,t):r) e = replaceRepeatedly r $ replace' s t e

-- | Takes in a theory and a translation function and repeatedly (to fixpoint) attempts to simplify (extend) it.
simplifyTheory
  :: (MultiTyMap '[Ord] '[var, ty, sym, en, fk, att, gen, sk])
  => Theory var ty sym en fk att gen sk
  -> [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)]
  -> (Theory var ty sym en fk att gen sk, [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)])
simplifyTheory th subst0 = case simplifyTheoryStep th of
  Nothing            -> (th, subst0)
  Just (th', subst1) -> simplifyTheory th' $ subst0 ++ [subst1]

-- | Does a one step simplifcation of a theory, looking for equations @gen/sk = term@, yielding also a
-- translation function from the old theory to the new, encoded as a list of (symbol, term) pairs.
simplifyTheoryStep
  :: (MultiTyMap '[Ord] '[var, ty, sym, en, fk, att, gen, sk])
  => Theory var ty sym en fk att gen sk
  -> Maybe (Theory var ty sym en fk att gen sk, (Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk))
simplifyTheoryStep eqs = case findSimplifiableEqs eqs of
  Nothing -> Nothing
  Just (toRemove, replacer) -> let
    eqs2 = Set.map    (\(ctx, EQ (lhs, rhs)) -> (ctx, EQ (replace' toRemove replacer lhs, replace' toRemove replacer rhs))) eqs
    eqs3 = Set.filter (\(_  , EQ (x,   y  )) -> not $ x == y) eqs2
    in Just (eqs3, (toRemove, replacer))

---------------------------------------------------------------------------------------------------------
-- Typesafe conversion

class Up x y where
  upgr :: x -> y

upp :: (Up var var', Up ty ty', Up sym sym', Up en en', Up fk fk', Up att att', Up gen gen', Up sk sk')
  => Term var  ty  sym  en  fk  att  gen  sk
  -> Term var' ty' sym' en' fk' att' gen' sk'
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

--------------------------------------------------------------------------------------------------------------------
-- Theories

type Theory var ty sym en fk att gen sk = Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk)

-- TODO wrap Map class to throw an error (or do something less ad hoc) if a key is ever put twice
type Ctx k v = Map k v

-- Our own pair type for pretty printing purposes
newtype EQ var ty sym en fk att gen sk
  = EQ (Term var ty sym en fk att gen sk, Term var ty sym en fk att gen sk) deriving (Ord,Eq)

instance TyMap Show '[var, ty, sym, en, fk, att, gen, sk] => Show (EQ var ty sym en fk att gen sk) where
  show (EQ (lhs,rhs)) = show lhs ++ " = " ++ show rhs

deriving instance TyMap Eq '[var, sym, fk, att, gen, sk] => Eq (Term var ty sym en fk att gen sk)

hasTypeType' :: EQ Void ty sym en fk att gen sk -> Bool
hasTypeType' (EQ (lhs, _)) = hasTypeType lhs
