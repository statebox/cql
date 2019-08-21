
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
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DuplicateRecordFields  #-}
{-# LANGUAGE ExplicitForAll         #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE ImpredicativeTypes     #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE LiberalTypeSynonyms    #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}

module Language.CQL where

import           Control.Concurrent
import           Control.DeepSeq
import           Control.Exception
import           Data.List                          (nub)
import qualified Data.Map.Strict                    as Map
import           Data.Maybe
import           Data.Typeable
import           Language.CQL.Common                as C
import           Language.CQL.Graph
import           Language.CQL.Instance              as I
import qualified Language.CQL.Instance.Presentation as IP
import           Language.CQL.Mapping               as M
import           Language.CQL.Options
import           Language.CQL.Parser.Program        (parseProgram)
import           Language.CQL.Program               as P
import           Language.CQL.Query                 as Q
import           Language.CQL.Schema                as S
import           Language.CQL.Term                  as Term
import           Language.CQL.Transform             as Tr
import           Language.CQL.Typeside              as T
import           Prelude                            hiding (EQ, exp)
import           System.IO.Unsafe

-- | Times out a computation after @i@ microseconds.
timeout' :: NFData x => Integer -> Err x -> Err x
timeout' i p = unsafePerformIO $ do
  m <- newEmptyMVar
  computer <- forkIO $ f m p
  _        <- forkIO $ s m computer
  takeMVar m
  where
    secs   = (fromIntegral i) * 1000000
    f m p0 = do
      x <- evaluate $ force p0
      putMVar m x
    s m c  = do
      threadDelay secs
      x <- tryTakeMVar m
      case x of
        Just y -> putMVar m y
        Nothing -> do
          putMVar m $ Left $ "Timeout after " ++ show i ++ " seconds."
          killThread c

-----------------------------------------------------------------------------------------------------------------
-- Type checking

class Typecheck e e' where
  typecheck :: Types -> e -> Err e'

-- | Checks that e.g. in @sigma F I@ that @F : S -> T@ and @I : S-Inst@.
-- Checking that @S@ is well-formed is done by 'validate'.
typecheckCqlProgram :: [(String,Kind)] -> Prog -> Types -> Err Types
typecheckCqlProgram [] _ x = pure x
typecheckCqlProgram ((v, k):l) prog ts = do
  m <- getKindCtx prog v k
  t <- wrapError ("Type Error in " ++ v ++ ": ") $ typecheck' v ts m
  typecheckCqlProgram l prog t

typecheck' :: String -> Types -> Exp -> Err Types
typecheck' v ts e = case e of
  ExpTy e' -> do { t <- typecheck ts e'; return $ ts { typesides  = Map.insert v t $ typesides  ts } }
  ExpS  e' -> do { t <- typecheck ts e'; return $ ts { schemas    = Map.insert v t $ schemas    ts } }
  ExpI  e' -> do { t <- typecheck ts e'; return $ ts { instances  = Map.insert v t $ instances  ts } }
  ExpM  e' -> do { t <- typecheck ts e'; return $ ts { mappings   = Map.insert v t $ mappings   ts } }
  ExpT  e' -> do { t <- typecheck ts e'; return $ ts { transforms = Map.insert v t $ transforms ts } }
  ExpQ  e' -> do { t <- typecheck ts e'; return $ ts { queries    = Map.insert v t $ queries    ts } }

instance Typecheck TypesideExp TypesideExp where
  typecheck = typecheckTypesideExp

instance Typecheck SchemaExp TypesideExp where
  typecheck = typecheckSchemaExp

instance Typecheck InstanceExp SchemaExp where
  typecheck = typecheckInstExp

instance Typecheck MappingExp (SchemaExp, SchemaExp) where
  typecheck = typecheckMapExp

instance Typecheck TransformExp (InstanceExp, InstanceExp) where
  typecheck = typecheckTransExp

instance Typecheck QueryExp (SchemaExp, SchemaExp) where
  typecheck = error "todo typecheck query exp"

typecheckTransExp :: Types -> TransformExp -> Err (InstanceExp, InstanceExp)
typecheckTransExp p (TransformVar v) = note ("Undefined transform: " ++ show v) $ Map.lookup v $ transforms p
typecheckTransExp _ (TransformId  s) = pure (s, s)

typecheckTransExp p (TransformComp f g) = do
  (a, b) <- typecheckTransExp p f
  (c, d) <- typecheckTransExp p g
  if   b == c
  then pure (a, d)
  else Left "Transform composition has non equal intermediate transforms"

typecheckTransExp p (TransformSigma f' h o) = do
  (s, _) <- typecheckMapExp p f'
  (i, j) <- typecheckTransExp p h
  s'     <- typecheckInstExp p i
  if   s == s'
  then pure (InstanceSigma f' i o, InstanceSigma f' j o)
  else Left "Source of mapping does not match instance schema"

typecheckTransExp p (TransformSigmaDeltaUnit f' i o) = do
  (s, _) <- typecheckMapExp p f'
  x      <- typecheckInstExp p i
  if   s == x
  then pure (i, InstanceDelta f' (InstanceSigma f' i o) o)
  else Left "Source of mapping does not match instance schema"

typecheckTransExp p (TransformSigmaDeltaCoUnit f' i o) = do
  (_, t) <- typecheckMapExp p f'
  x      <- typecheckInstExp p i
  if   t == x
  then pure (i, InstanceSigma f' (InstanceDelta f' i o) o)
  else Left "Target of mapping does not match instance schema"

typecheckTransExp p (TransformDelta f' h o) = do
  (_, t) <- typecheckMapExp   p f'
  (i, j) <- typecheckTransExp p h
  t'     <- typecheckInstExp  p i
  if   t == t'
  then pure (InstanceDelta f' i o, InstanceDelta f' j o)
  else Left "Target of mapping does not match instance schema"

typecheckTransExp p (TransformRaw r) = do
  l' <- typecheckInstExp p $ transraw_src r
  r' <- typecheckInstExp p $ transraw_dst r
  if   l' == r'
  then pure (transraw_src r, transraw_src r)
  else Left "Mapping has non equal schemas"

typecheckTransExp _ _ = error "todo"

typecheckMapExp :: Types -> MappingExp -> Err (SchemaExp, SchemaExp)
typecheckMapExp p (MappingVar v) = note ("Undefined mapping: " ++ show v) $ Map.lookup v $ mappings p
typecheckMapExp p (MappingComp f g) = do
  (a, b) <- typecheckMapExp p f
  (c, d) <- typecheckMapExp p g
  if   b == c
  then pure (a, d)
  else Left "Mapping composition has non equal intermediate schemas"

typecheckMapExp p (MappingId s) = do
  _ <- typecheckSchemaExp p s
  pure (s, s)
typecheckMapExp p (MappingRaw r) = do
  l' <- typecheckSchemaExp p $ mapraw_src r
  r' <- typecheckSchemaExp p $ mapraw_dst r
  if   l' == r'
  then pure (mapraw_src r, mapraw_dst r)
  else Left "Mapping has non equal typesides"

typecheckInstExp :: Types -> InstanceExp -> Err SchemaExp
typecheckInstExp p (InstanceVar v) = note ("Undefined instance: " ++ show v) $ Map.lookup v $ instances p
typecheckInstExp _ (InstanceInitial s) = pure s
typecheckInstExp _ (InstanceRaw r) = pure $ instraw_schema r
typecheckInstExp p (InstanceSigma f' i _) = do
  (s, t) <- typecheckMapExp p f'
  s'     <- typecheckInstExp p i
  if s == s'
  then pure t
  else Left "(Sigma): Instance not on mapping source."
typecheckInstExp p (InstanceDelta f' i _) = do
  (s, t) <- typecheckMapExp p f'
  t'     <- typecheckInstExp p i
  if   t == t'
  then pure s
  else Left "(Delta): Instance not on mapping target."
typecheckInstExp _ (InstancePivot _) = undefined --todo: requires breaking import cycle

typecheckInstExp _ _ = error "todo"

typecheckTypesideExp :: Types -> TypesideExp -> Err TypesideExp
typecheckTypesideExp p x = case x of
  TypesideSql     -> pure   TypesideSql
  TypesideInitial -> pure   TypesideInitial
  TypesideRaw r   -> pure $ TypesideRaw r
  TypesideVar v   -> note ("Undefined typeside: " ++ show v) $ Map.lookup v $ typesides p

typecheckSchemaExp
  :: Types -> SchemaExp -> Either String TypesideExp
typecheckSchemaExp p x = case x of
  SchemaRaw r      -> pure $ schraw_ts r
  SchemaVar v      -> note ("Undefined schema: " ++ show v) $ Map.lookup v $ schemas p
  SchemaInitial t  -> do { _ <- typecheckTypesideExp p t ; return t }
  SchemaCoProd l r -> do
    l' <- typecheckSchemaExp p l
    r' <- typecheckSchemaExp p r
    if l' == r'
    then return l'
    else Left "Coproduct has non equal typesides"


------------------------------------------------------------------------------------------------------------
-- evaluation

-- | The result of evaluating an CQL program.
type Env = KindCtx TypesideEx SchemaEx InstanceEx MappingEx QueryEx TransformEx Options

-- | Parse, typecheck, and evaluate the CQL program.
runProg :: String -> Err (Prog, Types, Env)
runProg srcText = do
  progE  <- parseProgram srcText
  opts   <- toOptions defaultOptions $ other progE
  o      <- findOrder progE
  typesE <- typecheckCqlProgram o progE newTypes
  envE   <- evalCqlProgram      o progE $ newEnv opts
  return (progE, typesE, envE)

evalCqlProgram :: [(String,Kind)] -> Prog -> Env -> Err Env
evalCqlProgram [] _ env = pure env
evalCqlProgram ((v,k):l) prog env = do
  e   <- getKindCtx prog v k
  ops <- toOptions (other env) $ getOptions' e
  t   <- wrapError ("Eval Error in " ++ v) $ timeout' (iOps ops Timeout) $ eval' prog env e
  evalCqlProgram l prog $ setEnv env v t

findOrder :: Prog -> Err [(String, Kind)]
findOrder p@(KindCtx t s i m q tr _) = do
  ret <- tsort g
  pure $ reverse ret
  where
    g       = Graph (allVars p) $ nub $ f0 t TYPESIDE ++ f0 s SCHEMA ++ f0 i INSTANCE ++ f0 m MAPPING ++ f0 q QUERY ++ f0 tr TRANSFORM
    f0 m0 k = concatMap (\(v,e) -> [ ((v,k),x) | x <- deps e ]) $ Map.toList m0

class Evalable e e' | e' -> e, e -> e' where
  validate :: e' -> Err ()
  eval :: Prog -> Env -> e -> Err e'
  getOptions :: e -> [(String, String)]

eval' :: Prog -> Env -> Exp -> Err Val
eval' p env e = case e of
  ExpTy e' -> do { x <- eval p env e'; maybeValidate x; return $ ValTy x }
  ExpS  e' -> do { x <- eval p env e'; maybeValidate x; return $ ValS  x }
  ExpI  e' -> do { x <- eval p env e'; maybeValidate x; return $ ValI  x }
  ExpM  e' -> do { x <- eval p env e'; maybeValidate x; return $ ValM  x }
  ExpT  e' -> do { x <- eval p env e'; maybeValidate x; return $ ValT  x }
  ExpQ  e' -> do { x <- eval p env e'; maybeValidate x; return $ ValQ  x }
  where
    maybeValidate :: Evalable exp val => val -> Err ()
    maybeValidate val = do
      ops <- toOptions (other env) $ getOptions' e
      if bOps ops Dont_Validate_Unsafe then return () else validate val


getKindCtx :: Prog -> String -> Kind -> Err Exp
getKindCtx g v k = case k of
  TYPESIDE  -> fmap ExpTy $ n $ Map.lookup v $ typesides  g
  SCHEMA    -> fmap ExpS  $ n $ Map.lookup v $ schemas    g
  INSTANCE  -> fmap ExpI  $ n $ Map.lookup v $ instances  g
  MAPPING   -> fmap ExpM  $ n $ Map.lookup v $ mappings   g
  TRANSFORM -> fmap ExpT  $ n $ Map.lookup v $ transforms g
  QUERY     -> fmap ExpQ  $ n $ Map.lookup v $ queries    g
  _         -> error "todo"
  where
    n :: forall x. Maybe x -> Err x
    n = note ("Undefined " ++ show k ++ ": " ++ v)

setEnv :: Env -> String -> Val -> Env
setEnv env v val  = case val of
  ValTy t -> env { typesides  = Map.insert v t $ typesides  env }
  ValS  t -> env { schemas    = Map.insert v t $ schemas    env }
  ValI  t -> env { instances  = Map.insert v t $ instances  env }
  ValM  t -> env { mappings   = Map.insert v t $ mappings   env }
  ValT  t -> env { transforms = Map.insert v t $ transforms env }
  ValQ  t -> env { queries    = Map.insert v t $ queries    env }

instance Evalable TypesideExp TypesideEx where
  validate (TypesideEx x) = typecheckTypeside x
  eval = evalTypeside
  getOptions = getOptionsTypeside

instance Evalable SchemaExp SchemaEx where
  validate (SchemaEx x) = typecheckSchema x
  eval = evalSchema
  getOptions = getOptionsSchema

instance Evalable InstanceExp InstanceEx where
  validate (InstanceEx x) = do
    IP.typecheck (schema x) (pres x)
    I.satisfiesSchema x
  eval prog env exp = do
    i  <- evalInstance prog env exp
    o' <- toOptions (other env) $ getOptions exp
    _  <- checkCons i $ bOps o' Require_Consistency
    pure i
    where
      checkCons (InstanceEx i) True  = if freeTalg i
        then pure ()
        else Left "Warning: type algebra not free. Set require_consistency = false to continue."
      checkCons _ False = pure ()
  getOptions = getOptionsInstance

instance Evalable MappingExp MappingEx where
  validate (MappingEx x) = typecheckMapping x
  eval = evalMapping
  getOptions = getOptionsMapping

instance Evalable TransformExp TransformEx where
  validate (TransformEx x) = typecheckTransform x
  eval = evalTransform
  getOptions = getOptionsTransform

instance Evalable QueryExp QueryEx where
  validate (QueryEx x) = typecheckQuery x
  eval = evalQuery
  getOptions = getOptionsQuery

getOptions' :: Exp -> [(String, String)]
getOptions' e = case e of
  ExpTy e' -> getOptions e'
  ExpS  e' -> getOptions e'
  ExpI  e' -> getOptions e'
  ExpM  e' -> getOptions e'
  ExpT  e' -> getOptions e'
  ExpQ  e' -> getOptions e'

------------------------------------------------------------------------------------------------------------

evalTypeside :: Prog -> Env -> TypesideExp -> Err TypesideEx
evalTypeside _ _ TypesideInitial = pure $ TypesideEx initialTypeside

evalTypeside p e (TypesideRaw r) = do
  x <- mapM (evalTypeside p e) $ tsraw_imports r
  evalTypesideRaw (other e) r x

evalTypeside _ env (TypesideVar v) = case Map.lookup v $ typesides env of
  Nothing             -> Left $ "Undefined typeside: " ++ show v
  Just (TypesideEx e) -> Right $ TypesideEx e

evalTypeside _ _ TypesideSql = pure $ TypesideEx $ sqlTypeside


evalTransform :: Prog -> Env -> TransformExp -> Err TransformEx
evalTransform _ env (TransformVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ transforms env

evalTransform p env (TransformId s) = do
  (InstanceEx i) <- evalInstance p env s
  pure $ TransformEx $ Transform i i (h i) (g i)
  where
    h i = foldr (\(gen,_) m -> Map.insert gen (Gen gen) m) Map.empty $ Map.toList $ IP.gens $ pres i
    g i = foldr (\(sk ,_) m -> Map.insert sk  (Sk  sk)  m) Map.empty $ Map.toList $ IP.sks  $ pres i

evalTransform p env (TransformComp f g) = do
  (TransformEx (f' :: Transform var  ty  sym  en  fk  att  gen  sk  x  y  gen'  sk'  x'  y' )) <- evalTransform p env f
  (TransformEx (g' :: Transform var2 ty2 sym2 en2 fk2 att2 gen2 sk2 x2 y2 gen'2 sk'2 x'2 y'2)) <- evalTransform p env g
  z <- composeTransform f' (fromJust (cast g' :: Maybe (Transform var ty sym en fk att gen' sk' x' y' gen'2 sk'2 x'2 y'2)))
  pure $ TransformEx z

evalTransform p env (TransformRaw r) = do
  InstanceEx s <- evalInstance p env $ transraw_src r
  InstanceEx (t :: Instance var ty sym en fk att gen sk x y) <- evalInstance p env $ transraw_dst r
  is <- mapM (evalTransform p env) $ transraw_imports r
  evalTransformRaw (fromJust (cast s)::Instance var ty sym en fk att gen sk x y) t r is

evalTransform prog env (TransformSigma f' i o) = do
  (MappingEx (f''  :: Mapping   var   ty   sym   en   fk   att   en' fk' att')) <- evalMapping prog env f'
  (TransformEx (i' :: Transform var'' ty'' sym'' en'' fk'' att'' gen sk x y gen' sk' x' y')) <- evalTransform prog env i
  o' <- toOptions (other env) o
  r <- evalSigmaTrans f'' (fromJust (cast i' :: Maybe (Transform var ty sym en fk att gen sk x y gen' sk' x' y'))) o'
  pure $ TransformEx r

evalTransform prog env (TransformDelta f' i o) = do
  (MappingEx (f''  :: Mapping   var   ty   sym   en'  fk'  att'  en  fk att)) <- evalMapping prog env f'
  (TransformEx (i' :: Transform var'' ty'' sym'' en'' fk'' att'' gen sk x y gen' sk' x' y')) <- evalTransform prog env i
  o' <- toOptions (other env) o
  r  <- evalDeltaTrans f'' (fromJust (cast i' :: Maybe (Transform var ty sym en fk att gen sk x y gen' sk' x' y'))) o'
  pure $ TransformEx r

evalTransform prog env (TransformSigmaDeltaUnit f' i o) = do
  (MappingEx (f'' :: Mapping  var   ty   sym   en   fk   att   en' fk' att')) <- evalMapping  prog env f'
  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk  x y )) <- evalInstance prog env i
  o' <- toOptions (other env) o
  r  <- evalDeltaSigmaUnit f'' (fromJust (cast i' :: Maybe (Instance var ty sym en fk att gen sk x y))) o'
  pure $ TransformEx r

evalTransform prog env (TransformSigmaDeltaCoUnit f' i o) = do
  (MappingEx (f'' :: Mapping  var   ty   sym   en   fk   att   en' fk' att')) <- evalMapping  prog env f'
  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk  x y )) <- evalInstance prog env i
  o' <- toOptions (other env) o
  r  <- evalDeltaSigmaCoUnit f'' (fromJust (cast i' :: Maybe (Instance var ty sym en' fk' att' gen sk x y))) o'
  pure $ TransformEx r

evalTransform _ _ _ = error "todo"


evalMapping :: Prog -> Env -> MappingExp -> Err MappingEx
evalMapping _ env (MappingVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ mappings env

evalMapping p env (MappingComp f g) = do
  (MappingEx (f' :: Mapping var  ty  sym  en  fk  att  en'  fk'  att' )) <- evalMapping p env f
  (MappingEx (g' :: Mapping var2 ty2 sym2 en2 fk2 att2 en'2 fk'2 att'2)) <- evalMapping p env g
  z <- composeMapping f' $ (fromJust (cast g' :: Maybe (Mapping var ty sym en' fk' att' en'2 fk'2 att'2)))
  pure $ MappingEx z

evalMapping p env (MappingId  s) = do
  (SchemaEx s') <- evalSchema p env s
  pure $ MappingEx $ foldr
    (\en' (Mapping s'' t e f' a) -> Mapping s'' t (Map.insert en' en' e) (f'' en' s' f') (g' en' s' a))
    (Mapping s' s' Map.empty Map.empty Map.empty) (S.ens s')
  where
    f'' en' s' f''' = foldr (\(fk, _) m -> Map.insert fk (Fk  fk $ Var ()) m) f''' $ fksFrom'  s' en'
    g'  en' s' f''' = foldr (\(fk, _) m -> Map.insert fk (Att fk $ Var ()) m) f''' $ attsFrom' s' en'

evalMapping p env (MappingRaw r) = do
  SchemaEx s <- evalSchema p env $ mapraw_src r
  SchemaEx (t::Schema var ty sym en fk att) <- evalSchema p env $ mapraw_dst r
  ix <- mapM (evalMapping p env) $ mapraw_imports r
  evalMappingRaw (fromJust (cast s) :: Schema var ty sym en fk att) t r ix

evalQuery :: Prog -> Env -> QueryExp -> Err QueryEx
evalQuery _ env (QueryVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ queries env
evalQuery _ _ _ = error "todo"

evalSchema :: Prog -> Env -> SchemaExp -> Err SchemaEx
evalSchema _ env (SchemaVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ schemas env

evalSchema prog env (SchemaInitial ts) = do
  TypesideEx ts'' <- evalTypeside prog env ts
  pure $ SchemaEx $ typesideToSchema ts''
evalSchema prog env (SchemaRaw r) = do
  TypesideEx t' <- evalTypeside prog env $ schraw_ts r
  x <- mapM (evalSchema prog env) $ schraw_imports r
  evalSchemaRaw (other env) t' r x

evalSchema _ _ _ = undefined


evalInstance :: Prog -> Env -> InstanceExp -> Either String InstanceEx
evalInstance _    env (InstanceVar   v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ instances env

evalInstance prog env (InstancePivot i) = do
  InstanceEx i' <- evalInstance prog env i
  let (_, i'', _) = pivot i'
  return $ InstanceEx i''

evalInstance prog env (InstanceInitial s) = do
  SchemaEx ts'' <- evalSchema prog env s
  pure $ InstanceEx $ emptyInstance ts''

evalInstance prog env (InstanceRaw r) = do
  SchemaEx t' <- evalSchema prog env $ instraw_schema r
  i <- mapM (evalInstance prog env) (instraw_imports r)
  evalInstanceRaw (other env) t' r i

evalInstance prog env (InstanceSigma f' i o) = do
  (MappingEx (f'' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping prog env f'
  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk x y)) <- evalInstance prog env i
  o' <- toOptions (other env) o
  r  <- evalSigmaInst f'' (fromJust (cast i' :: Maybe (Instance var ty sym en fk att gen sk x y))) o'
  return $ InstanceEx r

evalInstance prog env (InstanceDelta f' i o) = do
  (MappingEx (f'' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping prog env f'
  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk x y)) <- evalInstance prog env i
  o' <- toOptions (other env) o
  r  <- evalDeltaInst f'' (fromJust (cast i' :: Maybe (Instance var ty sym en' fk' att' gen sk x y))) o'
  return $ InstanceEx r

evalInstance _ _ _ = error "todo"
