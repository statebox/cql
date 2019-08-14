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

module Language.CQL.Collage where

import           Control.DeepSeq       (NFData)
import           Data.Map.Merge.Strict
import           Data.Map.Strict       as Map hiding (foldr, size)
import           Data.Set              as Set hiding (foldr, size)
import           Data.Void
import           Language.CQL.Common
import           Language.CQL.Term     (Head(..), Term(..), simplifyFix, occsTerm, upp)
import           Language.CQL.Term     (EQ(..), Ctx)
import           Prelude               hiding (EQ)

data Collage var ty sym en fk att gen sk
  = Collage
  { ceqs  :: Set (Ctx var (ty+en), EQ var ty sym en fk att gen sk)
  , ctys  :: Set ty
  , cens  :: Set en
  , csyms :: Map sym ([ty],ty)
  , cfks  :: Map fk (en, en)
  , catts :: Map att (en, ty)
  , cgens :: Map gen en
  , csks  :: Map sk ty
  } deriving (Eq, Show)

--------------------------------------------------------------------------------

occs
  :: (Ord sym, Ord fk, Ord att, Ord gen, Ord sk)
  => Collage var ty sym en fk att gen sk
  -> Map (Head ty sym en fk att gen sk) Int
occs col = foldr (\(_, EQ (lhs, rhs)) x -> m x $ m (occsTerm lhs) $ occsTerm rhs) Map.empty $ ceqs col
  where
    m = merge preserveMissing preserveMissing $ zipWithMatched (\_ x y -> x + y)

--------------------------------------------------------------------------------

-- | Simplify a collage by replacing symbols of the form @gen/sk = term@, yielding also a
--   translation function from the old theory to the new, encoded as a list of (symbol, term) pairs.
simplify
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, gen, sk])
  =>  Collage var ty sym en fk att gen sk
  -> (Collage var ty sym en fk att gen sk, [(Head ty sym en fk att gen sk, Term var ty sym en fk att gen sk)])
simplify (Collage ceqs'  ctys' cens' csyms' cfks' catts' cgens'  csks'    )
  =         (Collage ceqs'' ctys' cens' csyms' cfks' catts' cgens'' csks'', f)
  where
    (ceqs'', f) = simplifyFix ceqs' []
    cgens''     = Map.fromList $ Prelude.filter (\(x,_) -> notElem (HGen x) $ fmap fst f) $ Map.toList cgens'
    csks''      = Map.fromList $ Prelude.filter (\(x,_) -> notElem (HSk  x) $ fmap fst f) $ Map.toList csks'

--------------------------------------------------------------------------------

eqsAreGround :: Collage var ty sym en fk att gen sk -> Bool
eqsAreGround col = Prelude.null [ x | x <- Set.toList $ ceqs col, not $ Map.null (fst x) ]

fksFrom :: Eq en => Collage var ty sym en fk att gen sk -> en -> [(fk,en)]
fksFrom sch en' = f $ Map.assocs $ cfks sch
  where f []               = []
        f ((fk,(en1,t)):l) = if en1 == en' then (fk,t) : (f l) else f l

attsFrom :: Eq en => Collage var ty sym en fk att gen sk -> en -> [(att,ty)]
attsFrom sch en' = f $ Map.assocs $ catts sch
  where f []               = []
        f ((fk,(en1,t)):l) = if en1 == en' then (fk,t) : (f l) else f l

-- | Gets the type of a term that is already known to be well-typed.
typeOf
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Term Void Void Void en fk Void gen Void
  -> en
typeOf col e = case typeOf' col Map.empty (upp e) of
  Left _ -> error "Impossible in typeOf, please report."
  Right x -> case x of
    Left _  -> error "Impossible in typeOf, please report."
    Right y -> y

checkDoms
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Err ()
checkDoms col = do
  mapM_ f    $ Map.elems $ csyms col
  mapM_ g    $ Map.elems $ cfks  col
  mapM_ h    $ Map.elems $ catts col
  mapM_ isEn $ Map.elems $ cgens col
  mapM_ isTy $ Map.elems $ csks  col
  where
    f (t1,t2) = do { mapM_ isTy t1 ; isTy t2 }
    g (e1,e2) = do { isEn e1 ; isEn e2 }
    h (e ,t ) = do { isEn e ; isTy t }
    isEn x  = if Set.member x $ cens col
      then pure ()
      else Left $ "Not an entity: " ++ show x
    isTy x  = if Set.member x $ ctys col
      then pure ()
      else Left $ "Not a type: "    ++ show x

typeOfCol
  :: (MultiTyMap '[Show, Ord, NFData] '[var, ty, sym, en, fk, att, gen, sk])
  => Collage var ty sym en fk att gen sk
  -> Err ()
typeOfCol col = do
  checkDoms col
  mapM_ (typeOfEq' col) $ Set.toList $ ceqs col

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

-- | Initialize a mapping of sorts to bools for sort inhabition check.
initGround :: (Ord ty, Ord en) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool)
initGround col = (me', mt')
  where
    me  = Map.fromList $ Prelude.map (\en -> (en, False)) $ Set.toList $ cens col
    mt  = Map.fromList $ Prelude.map (\ty -> (ty, False)) $ Set.toList $ ctys col
    me' = Prelude.foldr (\(_, en) m -> Map.insert en True m) me $ Map.toList $ cgens col
    mt' = Prelude.foldr (\(_, ty) m -> Map.insert ty True m) mt $ Map.toList $ csks  col

-- | Applies one layer of symbols to the sort to boolean inhabitation map.
closeGround :: (Ord ty, Ord en) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool) -> (Map en Bool, Map ty Bool)
closeGround col (me, mt) = (me', mt'')
  where
    mt''= Prelude.foldr (\(_, (tys,ty)) m -> if and ((!) mt' <$> tys) then Map.insert ty True m else m) mt' $ Map.toList $ csyms col
    mt' = Prelude.foldr (\(_, (en, ty)) m -> if (!) me' en then Map.insert ty True m else m)            mt  $ Map.toList $ catts col
    me' = Prelude.foldr (\(_, (en, _ )) m -> if (!) me  en then Map.insert en True m else m)            me  $ Map.toList $ cfks  col

-- | Does a fixed point of closeGround.
iterGround :: (MultiTyMap '[Show, Ord, NFData] '[ty, en]) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool) -> (Map en Bool, Map ty Bool)
iterGround col r = if r == r' then r else iterGround col r'
 where r' = closeGround col r

-- | Gets the inhabitation map for the sorts of a collage.
computeGround :: (MultiTyMap '[Show, Ord, NFData] '[ty, en]) => Collage var ty sym en fk att gen sk -> (Map en Bool, Map ty Bool)
computeGround col = iterGround col $ initGround col

-- | True iff all sorts in a collage are inhabited.
allSortsInhabited :: (MultiTyMap '[Show, Ord, NFData] '[ty, en]) => Collage var ty sym en fk att gen sk -> Bool
allSortsInhabited col = t && f
 where (me, mt) = computeGround col
       t = and $ Map.elems me
       f = and $ Map.elems mt
