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

module Language.CQL.Morphism where

import           Control.DeepSeq
import           Data.Map.Strict       as Map hiding (foldr, size)
import           Data.Maybe
import           Data.Set              as Set hiding (foldr, size)
import           Data.Void
import           Language.CQL.Common
import           Language.CQL.Term     (Collage(..), Ctx, Term(..), EQ(..), subst, upp)
import           Prelude               hiding (EQ)


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

-- | Checks totality of the morphism mappings.
checkDoms'
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, gen, sk, en', fk', att', gen', sk'])
  => Morphism var ty sym en fk att gen sk en' fk' att' gen' sk'
  -> Err ()
checkDoms' mor = do
  mapM_ e $ Set.toList $ cens  $ m_src mor
  mapM_ f $ Map.keys   $ cfks  $ m_src mor
  mapM_ a $ Map.keys   $ catts $ m_src mor
  mapM_ g $ Map.keys   $ cgens $ m_src mor
  mapM_ s $ Map.keys   $ csks  $ m_src mor
  where
    e en = if Map.member en $ m_ens  mor then pure () else Left $ "No entity mapping for " ++ show en
    f fk = if Map.member fk $ m_fks  mor then pure () else Left $ "No fk mapping for "     ++ show fk
    a at = if Map.member at $ m_atts mor then pure () else Left $ "No att mapping for "    ++ show at
    g gn = if Map.member gn $ m_gens mor then pure () else Left $ "No gen mapping for "    ++ show gn
    s sk = if Map.member sk $ m_sks  mor then pure () else Left $ "No sk mapping for "     ++ show sk

-- | Translates a term along a morphism.
translate'
  :: forall var var' ty sym en fk att gen sk en' fk' att' gen' sk'
  .  TyMap Ord '[gen, sk, fk, var, att, var']
  => Morphism var ty sym en fk att gen sk en' fk' att' gen' sk'
  -> Term var' Void Void en  fk  Void gen  Void
  -> Term var' Void Void en' fk' Void gen' Void
translate' _   (Var x)  = Var x
translate' mor (Fk f a) = let
  x = translate' mor a    :: Term var' Void Void en' fk' Void gen' Void
  y = upp (m_fks mor ! f) :: Term ()   Void Void en' fk' Void gen' Void
  in subst y x
translate' mor (Gen g) = upp $ m_gens mor ! g
translate' _   (Sym _ _) = undefined
translate' _   (Att _ _) = undefined
translate' _   (Sk _   ) = undefined

-- | Translates a term along a morphism.
translate
  :: forall var var' ty sym en fk att gen sk en' fk' att' gen' sk'
  .  TyMap Ord '[gen, sk, fk, var, att, var']
  => Morphism var  ty sym en  fk  att  gen  sk en' fk' att' gen' sk'
  -> Term     var' ty sym en  fk  att  gen  sk
  -> Term     var' ty sym en' fk' att' gen' sk'
translate mor term = case term of
  Var x    -> Var x
  Sym f xs -> Sym f (translate mor <$> xs)
  Gen g    -> upp $ m_gens mor ! g
  Sk  s    -> upp $ m_sks mor  ! s
  Att f a  -> subst (upp $ m_atts mor ! f) $ translate mor a
  Fk  f a  -> subst (upp y) x
    where
      x = translate mor a :: Term var' ty sym  en' fk' att' gen' sk'
      y = m_fks mor ! f   :: Term () Void Void en' fk' Void Void Void


typeOfMor
  :: forall var ty sym en fk att gen sk en' fk' att' gen' sk'
  .  (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, gen, sk, en', fk', att', gen', sk'])
  => Morphism var ty sym en fk att gen sk en' fk' att' gen' sk'
  -> Err ()
typeOfMor mor  = do
  checkDoms' mor
  mapM_ typeOfMorEns $ Map.toList $ m_ens mor
  mapM_ typeOfMorFks $ Map.toList $ m_fks mor
  mapM_ typeOfMorAtts $ Map.toList $ m_atts mor
  mapM_ typeOfMorGens $ Map.toList $ m_gens mor
  mapM_ typeOfMorSks $ Map.toList $ m_sks mor
  where
    transE en = case (Map.lookup en (m_ens mor)) of
      Just x  -> x
      Nothing -> undefined
    typeOfMorEns (e,e') | elem e (cens $ m_src mor) && elem e' (cens $ m_dst mor) = pure ()
    typeOfMorEns (e,e') = Left $ "Bad entity mapping " ++ show e ++ " -> " ++ show e'
    typeOfMorFks :: (fk, Term () Void Void en' fk' Void Void Void) -> Err ()
    typeOfMorFks (fk,e) | Map.member fk (cfks $ m_src mor)
         = let (s,t) = fromJust $ Map.lookup fk $ cfks $ m_src mor
               (s',t') = (transE s, transE t)
           in do t0 <- typeOf' (m_dst mor) (Map.fromList [(Left (), Right s')]) $ upp e
                 if t0 == Right t' then pure () else Left $ "1Ill typed in " ++ show fk ++ ": " ++ show e
    typeOfMorFks (e,e') = Left $ "Bad fk mapping " ++ show e ++ " -> " ++ show e'
    typeOfMorAtts (att,e) | Map.member att (catts $ m_src mor)
         = let (s,t) = fromJust $ Map.lookup att $ catts $ m_src mor
               s' = transE s
           in do t0 <- typeOf' (m_dst mor) (Map.fromList [(Left (),Right s')]) $ upp e
                 if t0 == Left t then pure () else Left $ "2Ill typed attribute, " ++ show att ++ " expression " ++ show e
                  ++ ", computed type " ++ show t0 ++ " and required type " ++ show t
    typeOfMorAtts (e,e') = Left $ "Bad att mapping " ++ show e ++ " -> " ++ show e'
    typeOfMorGens (gen,e) | Map.member gen (cgens $ m_src mor)
         = let t = fromJust $ Map.lookup gen $ cgens $ m_src mor
               t' = transE t
           in do t0 <- typeOf' (m_dst mor) (Map.fromList []) $ upp e
                 if t0 == Right t' then pure () else Left $ "3Ill typed in " ++ show gen ++ ": " ++ show e
    typeOfMorGens (e,e') = Left $ "Bad gen mapping " ++ show e ++ " -> " ++ show e'
    typeOfMorSks (sk,e) | Map.member sk (csks $ m_src mor)
         = let t = fromJust $ Map.lookup sk $ csks $ m_src mor
           in do t0 <- typeOf' (m_dst mor) (Map.fromList []) $ upp e
                 if t0 == Left t then pure () else Left $ "4Ill typed in " ++ show sk ++ ": " ++ show e
    typeOfMorSks (e,e') = Left $ "Bad null mapping " ++ show e ++ " -> " ++ show e'


-- I've given up on non string based error handling for now
typeOf'
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Ctx var (ty + en)
  -> Term    var ty sym en fk att gen sk
  -> Err (ty + en)
typeOf' _ ctx (Var v) = note ("Unbound variable: " ++ show v) $ Map.lookup v ctx
typeOf' col _ (Gen g) = case Map.lookup g $ cgens col of
  Nothing -> Left  $ "Unknown generator: " ++ show g
  Just t  -> Right $ Right t
typeOf' col _ (Sk s) = case Map.lookup s $ csks col of
  Nothing -> Left  $ "Unknown labelled null: " ++ show s
  Just t  -> Right $ Left t
typeOf' col ctx xx@(Fk f a) = case Map.lookup f $ cfks col of
  Nothing     -> Left $ "Unknown foreign key: " ++ show f
  Just (s, t) -> do s' <- typeOf' col ctx a
                    if (Right s) == s' then pure $ Right t else Left $ "Expected argument to have entity " ++
                     show s ++ " but given " ++ show s' ++ " in " ++ (show xx)
typeOf' col ctx xx@(Att f a) = case Map.lookup f $ catts col of
  Nothing -> Left $ "Unknown attribute: " ++ show f
  Just (s, t) -> do s' <- typeOf' col ctx a
                    if (Right s) == s' then pure $ Left t else Left $ "Expected argument to have entity " ++
                     show s ++ " but given " ++ show s' ++ " in " ++ (show xx)
typeOf' col ctx xx@(Sym f a) = case Map.lookup f $ csyms col of
  Nothing -> Left $ "Unknown function symbol: " ++ show f
  Just (s, t) -> do s' <- mapM (typeOf' col ctx) a
                    if length s' == length s
                    then if (Left <$> s) == s'
                         then pure $ Left t
                         else Left $ "Expected arguments to have types " ++
                     show s ++ " but given " ++ show s' ++ " in " ++ (show $ xx)
                    else Left $ "Expected argument to have arity " ++
                     show (length s) ++ " but given " ++ show (length s') ++ " in " ++ (show $ xx)

typeOfEq'
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> (Ctx var (ty + en), EQ var ty sym en fk att gen sk)
  -> Err (ty + en)
typeOfEq' col (ctx, EQ (lhs, rhs)) = do
  lhs' <- typeOf' col ctx lhs
  rhs' <- typeOf' col ctx rhs
  if lhs' == rhs'
  then Right lhs'
  else Left  $ "Equation lhs has type " ++ show lhs' ++ " but rhs has type " ++ show rhs'
