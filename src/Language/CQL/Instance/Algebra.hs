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
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LiberalTypeSynonyms   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.CQL.Instance.Algebra where

import           Control.DeepSeq
import           Control.Monad
import qualified Data.Foldable         as Foldable
import           Data.List             as List hiding (intercalate)
import           Data.Map.Strict       (Map, (!))
import qualified Data.Map.Strict       as Map
import           Data.Set              (Set)
import qualified Data.Set              as Set
import           Data.Void
import           Language.CQL.Common   (intercalate, mapl, section, MultiTyMap, TyMap, type (+))
import           Language.CQL.Schema   as Schema
import           Language.CQL.Term     (EQ, Head(HSk), Term(..), subst, upp, replaceRepeatedly, simplifyTheory)
import           Language.CQL.Typeside as Typeside
import           Prelude               hiding (EQ)
import qualified Text.Tabular          as T
import qualified Text.Tabular.AsciiArt as Ascii


-- | An algebra (model) of a 'Schema'.
--
--   * For entities, consists of a carrier set, evaluation function @nf@, and its "inverse" @repr@.
--
--   * For types, consists of a generating set of labelled nulls, evaluation function @nf'@, and its "inverse" @repr'@,
--     as well as a set of equations (the so-called type algebra).
--
-- The @Eq@ instance is not defined because for now we define instance equality to be based on equations.
--
-- @x@: type of Carrier
-- @y@: type of generators for type algebra presentation
data Algebra var ty sym en fk att gen sk x y
  = Algebra
  { aschema :: Schema var ty sym en fk att

  , en      :: en -> Set x -- globally unique xs
  , aGen    :: gen -> x
  , aFk     :: fk  -> x -> x
  , repr    :: x   -> Term Void Void Void en fk Void gen Void

  , ty      :: ty -> Set y -- globally unique ys
  , nf'     :: sk + (x, att) -> Term Void ty sym Void Void Void Void y
  , repr'   :: y -> Term Void ty sym en fk att gen sk

  , teqs    :: Set (EQ Void ty sym Void Void Void Void y)
  }

instance (NFData var, NFData ty, NFData sym, NFData en, NFData fk, NFData att, NFData x, NFData y)
  => NFData (Algebra var ty sym en fk att gen sk x y)
  where
    rnf (Algebra s0 e0 nf0 nf02 repr0 ty0 nf1 repr1 eqs1) =
      deepseq s0 $ f e0 $ deepseq nf0 $ deepseq repr0 $ w ty0 $ deepseq nf1 $ deepseq repr1 $ deepseq nf02 $ rnf eqs1
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

-- | Helper to convert terms in the 'Collage' of entity sort into terms with 'Void's in the attribute etc slots.
--   Morally, 'Collage' should store two or more classes of equation, but having to convert like this is relatively rare.
--   Indeed, 'IP.satisfiesSchema' itself is redundant; a properly functioning CQL would not generate unsatisfying
--   instances.
down1
  :: Term x ty   sym  en fk att  gen sk
  -> Term x Void Void en fk Void gen Void
down1 (Var v)  = Var v
down1 (Gen g)  = Gen g
down1 (Fk f a) = Fk f (down1 a)
down1 _        = error "Anomaly: please report.  Function name: down1."



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
nf _ _           = error "Impossible, error in nf"

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


---------------------------------------------------------------------------------------------------------------
-- Initial algebras

-- | The carrier for the initial algebra of an instance; they are just terms.
--   Made into a separate type so this could be changed; cql-java for example just uses natural numbers as the carrier.
--   TODO should  be called ETerm, for 'entity term'.
type Carrier en fk gen = Term Void Void Void en fk Void gen Void

-- | The generating labelled nulls for the type algebra of the associated instance.
newtype TalgGen en fk att gen sk = MkTalgGen (Either sk (Carrier en fk gen, att))

-- | Inlines type-algebra equations of the form @gen = term@.
--   The hard work is delegated to functions from the 'Term' module.
simplify
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, gen, sk, x, y])
  => Algebra var ty sym en fk att gen sk x y
  -> Algebra var ty sym en fk att gen sk x y
simplify
  (Algebra sch en' nf''' nf'''2 repr''' ty'  nf''''  repr'''' teqs'   ) =
   Algebra sch en' nf''' nf'''2 repr''' ty'' nf''''' repr'''' teqs''''
    where
      teqs''       = Set.map (\x -> (Map.empty, x)) teqs'
      (teqs''', f) = simplifyTheory teqs'' []
      teqs''''     = Set.map snd teqs'''
      ty'' t       = Set.filter (\x -> notElem (HSk x) $ map fst f) $ ty' t
      nf''''' e    = replaceRepeatedly f $ nf'''' e

instance TyMap NFData '[en, fk, att, gen, sk] => NFData (TalgGen en fk att gen sk) where
  rnf (MkTalgGen x) = rnf x

instance TyMap Show '[en, fk, att, gen, sk] => Show (TalgGen en fk att gen sk) where
  show (MkTalgGen (Left  x)) = show x
  show (MkTalgGen (Right x)) = show x

deriving instance TyMap Ord '[en, fk, att, gen, sk] => Ord (TalgGen en fk att gen sk)

deriving instance TyMap Eq '[fk, att, gen, sk] => Eq (TalgGen en fk att gen sk)

---------------------------------------------------------------------------------------------------------------
-- Functorial data migration

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

mapGen :: (t1 -> t2) -> Term var ty sym en (t2 -> t2) att t1 sk -> t2
mapGen f (Gen g)   = f g
mapGen f (Fk fk a) = fk $ mapGen f a
mapGen _ _         = error "please report, error on mapGen"


-------------------------------------------------------------------------------------------------------------------
-- Printing

instance (TyMap Show '[var, ty, sym, en, fk, att, gen, sk, x, y], Eq en, Eq fk, Eq att)
  => Show (Algebra var ty sym en fk att gen sk x y) where
  show alg@(Algebra sch _ _ _ _ ty' _ _ teqs') =
    unlines $
      [ section "entities"     $ unlines prettyEntities
      , section "type-algebra" $ intercalate "\n" prettyTypeEqns
      , section "nulls"        $ intercalate "\n" w
      ]
    where
      w = mapl w2 . Typeside.tys . Schema.typeside $ sch
      w2 ty'' = show ty'' ++ " (" ++ (show . Set.size $ ty' ty'') ++ ") = " ++ show (Foldable.toList $ ty' ty'') ++ " "
      prettyEntities = prettyEntityTable alg `mapl` Schema.ens sch
      prettyTypeEqns = Set.map show teqs'

prettyEntity
  :: forall var ty sym en fk att gen sk x y
   . (TyMap Show '[ty, sym, en, fk, att, x, y], Eq en)
  => Algebra var ty sym en fk att gen sk x y
  -> en
  -> String
prettyEntity alg@(Algebra sch en' _ _ _ _ _ _ _) es =
  show es ++ " (" ++ (show . Set.size $ en' es) ++ ")\n" ++
  "--------------------------------------------------------------------------------\n" ++
  intercalate "\n" (prettyEntityRow es `mapl` en' es)
  where
    prettyEntityRow :: en -> x -> String
    prettyEntityRow en'' e =
      show e ++ ": " ++
      intercalate "," (prettyFk  e <$> fksFrom'  sch en'') ++ ", " ++
      intercalate "," (prettyAtt e <$> attsFrom' sch en'')

    prettyAtt :: x -> (att, w) -> String
    prettyAtt x (att,_) = show att ++ " = " ++ prettyTerm (aAtt alg att x)
    prettyFk  x (fk, _) = show fk  ++ " = " ++ show (aFk alg fk x)
    prettyTerm = show

-- TODO unquote identifiers; stick fks and attrs in separate `Group`s?
prettyEntityTable
  :: forall var ty sym en fk att gen sk x y
   . (TyMap Show '[ty, sym, en, fk, att, x, y], Eq en)
  => Algebra var ty sym en fk att gen sk x y
  -> en
  -> String
prettyEntityTable alg@(Algebra sch en' _ _ _ _ _ _ _) es =
  show es ++ " (" ++ show (Set.size (en' es)) ++ ")\n" ++
  Ascii.render show id id tbl
  where
    tbl :: T.Table x String String
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

    prettyAtt :: x -> (att, ty) -> String
    prettyAtt x (att,_) = prettyTerm $ aAtt alg att x

    prettyTerm = show
