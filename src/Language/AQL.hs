{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.AQL where

import Prelude hiding (EQ)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Language.Common as C
import Language.Term as Term
import Language.Schema as S
import Language.Instance as I
import Language.Mapping as M
import Language.Typeside as T
import Language.Transform as Tr
import Language.Query as Q
import Data.List (nub)
import Data.Maybe
import Language.Parser (parseAqlProgram)
import Language.Program as P
import Data.Void
import Data.Typeable
import Language.Options
import Control.Arrow (left)
import System.Timeout
import System.IO.Unsafe
import Control.Exception.Base
--import Control.DeepSeq

timeout' :: Integer -> Err x -> Err x
timeout' ms c = case c' of
  Nothing -> Left $ "Timeout after " ++ (show s) ++ " seconds."
  Just x' -> x'
  where
    c' = unsafePerformIO $ timeout s $! seq c (evaluate c) --not working
    s  = (fromIntegral ms) * 1000000

-- simple three phase evaluation and reporting
runProg :: String -> Err (Prog, Types, Env)
runProg p = do
  p1 <- parseAqlProgram p
  ops<- toOptions defaultOptions $ other p1
  o  <- findOrder p1
  p2 <- typecheckAqlProgram o p1 newTypes
  p3 <- evalAqlProgram o p1 (newEnv ops)
  return (p1, p2, p3)

type Env = KindCtx TypesideEx SchemaEx InstanceEx MappingEx QueryEx TransformEx Options

wrapError :: String -> Either String b -> Either String b
wrapError prefix se = (\s -> prefix ++ ": " ++ s) `left` se


class Typecheck e e' where
  typecheck :: Types -> e -> Err e'

-- some ordering - could be program order, but not necessarily
-- todo: could be backwards, will check w/ mappings, queries
typecheckAqlProgram :: [(String,Kind)] -> Prog -> Types -> Err Types
typecheckAqlProgram [] _ x = pure x
typecheckAqlProgram ((v,k):l) prog ts = do
  m <- getKindCtx prog v k
  t <- wrapError ("Type Error in " ++ v ++ ": ") $ typecheck' v ts m
  typecheckAqlProgram l prog t


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

typecheckTransExp _ (TransformId s) = pure (s, s)

typecheckTransExp p (TransformComp f g) = do
  (a,b) <- typecheckTransExp p f
  (c,d) <- typecheckTransExp p g
  if   b == c
  then pure $ (a, d)
  else Left "Transform composition has non equal intermediate transforms"

typecheckTransExp p (TransformSigma f' h o) = do
  (s,_) <- typecheckMapExp p f'
  (i,j) <- typecheckTransExp p h
  s' <- typecheckInstExp p i
  if s == s'
  then pure (InstanceSigma f' i o, InstanceSigma f' j o)
  else Left $ "Source of mapping does not match instance schema"

typecheckTransExp p (TransformSigmaDeltaUnit f' i o) = do
  (s,_) <- typecheckMapExp p f'
  x <- typecheckInstExp p i
  if s == x
  then pure (i, InstanceDelta f' (InstanceSigma f' i o) o)
  else Left $ "Source of mapping does not match instance schema"

typecheckTransExp p (TransformSigmaDeltaCoUnit f' i o) = do
  (_,t) <- typecheckMapExp p f'
  x <- typecheckInstExp p i
  if t == x
  then pure (i, InstanceSigma f' (InstanceDelta f' i o) o)
  else Left $ "Target of mapping does not match instance schema"

typecheckTransExp p (TransformDelta f' h o) = do
  (_,t) <- typecheckMapExp p f'
  (i,j) <- typecheckTransExp p h
  t' <- typecheckInstExp p i
  if t == t'
  then pure (InstanceDelta f' i o, InstanceDelta f' j o)
  else Left $ "Target of mapping does not match instance schema"

typecheckTransExp p (TransformRaw r) = do
  l' <- typecheckInstExp p $ transraw_src r
  r' <- typecheckInstExp p $ transraw_dst r
  if   l' == r'
  then pure $ (transraw_src r, transraw_src r)
  else Left "Mapping has non equal schemas"

typecheckTransExp _ _ = error "todo"

typecheckMapExp :: Types -> MappingExp -> Err (SchemaExp, SchemaExp)
typecheckMapExp p (MappingVar v) = note ("Undefined mapping: " ++ show v) $ Map.lookup v $ mappings p
typecheckMapExp p (MappingComp f g) = do
  (a,b) <- typecheckMapExp p f
  (c,d) <- typecheckMapExp p g
  if   b == c
  then pure $ (a, d)
  else Left "Mapping composition has non equal intermediate schemas"

typecheckMapExp p (MappingId s) = do
  _ <- typecheckSchemaExp p s
  pure (s, s)
typecheckMapExp p (MappingRaw r) = do
  l' <- typecheckSchemaExp p $ mapraw_src r
  r' <- typecheckSchemaExp p $ mapraw_dst r
  if   l' == r'
  then pure $ (mapraw_src r, mapraw_dst r)
  else Left "Mapping has non equal typesides"




typecheckInstExp :: Types -> InstanceExp -> Err SchemaExp
typecheckInstExp p (InstanceVar v) = note ("Undefined instance: " ++ show v) $ Map.lookup v $ instances p
typecheckInstExp _ (InstanceInitial s) = pure s
typecheckInstExp _ (InstanceRaw r) = pure $ instraw_schema r
typecheckInstExp p (InstanceSigma f' i _) = do
  (s,t) <- typecheckMapExp p f'
  s' <- typecheckInstExp p i
  if s == s'
  then pure t
  else Left "(Sigma): Instance not on mapping source."
typecheckInstExp p (InstanceDelta f' i _) = do
  (s,t) <- typecheckMapExp p f'
  t' <- typecheckInstExp p i
  if t == t'
  then pure s
  else Left "(Delta): Instance not on mapping target."

typecheckInstExp _ _ = undefined

typecheckTypesideExp :: Types -> TypesideExp -> Err TypesideExp
typecheckTypesideExp p (TypesideVar v) = note ("Undefined typeside: " ++ show v) $ Map.lookup v $ typesides p
typecheckTypesideExp _ TypesideInitial = pure TypesideInitial
typecheckTypesideExp _ (TypesideRaw r) = pure $ TypesideRaw r

typecheckSchemaExp
  :: Types -> SchemaExp -> Either String TypesideExp
typecheckSchemaExp _ (SchemaRaw r) = pure $ schraw_ts r
typecheckSchemaExp p (SchemaVar v) = note ("Undefined schema: " ++ show v) $ Map.lookup v $ schemas p
typecheckSchemaExp p (SchemaInitial t) = do
  _ <- typecheckTypesideExp p t
  return t
typecheckSchemaExp p (SchemaCoProd l r) = do
  l' <- typecheckSchemaExp p l
  r' <- typecheckSchemaExp p r
  if l' == r'
  then return l'
  else Left "Coproduct has non equal typesides"

getOptions' :: Exp -> [(String, String)]
getOptions' e = case e of
  ExpTy e' -> getOptions e'
  ExpS  e' -> getOptions e'
  ExpI  e' -> getOptions e'
  ExpM  e' -> getOptions e'
  ExpT  e' -> getOptions e'
  ExpQ  _  -> undefined

class Evalable e e' | e' -> e, e -> e' where
  validate :: e' -> Err ()
  eval :: Prog -> Env -> e -> Err e'
  getOptions :: e -> [(String, String)]

eval' :: Prog -> Env -> Exp -> Err Val
eval' p env e = case e of
  ExpTy e' -> do { x <- eval p env e'; validate x; return $ ValTy x }
  ExpS  e' -> do { x <- eval p env e'; validate x; return $ ValS  x }
  ExpI  e' -> do { x <- eval p env e'; validate x; return $ ValI  x }
  ExpM  e' -> do { x <- eval p env e'; validate x; return $ ValM  x }
  ExpT  e' -> do { x <- eval p env e'; validate x; return $ ValT  x }
  ExpQ  e' -> do { x <- eval p env e'; validate x; return $ ValQ  x }

getKindCtx :: Prog -> String -> Kind -> Err Exp
getKindCtx g v k = case k of
  TYPESIDE  -> fmap ExpTy $ n $ Map.lookup v $ typesides  g
  SCHEMA    -> fmap ExpS  $ n $ Map.lookup v $ schemas    g
  INSTANCE  -> fmap ExpI  $ n $ Map.lookup v $ instances  g
  MAPPING   -> fmap ExpM  $ n $ Map.lookup v $ mappings   g
  TRANSFORM -> fmap ExpT  $ n $ Map.lookup v $ transforms g
  QUERY     -> fmap ExpQ  $ n $ Map.lookup v $ queries    g
  _ -> error "todo"
  where
    n :: forall x. Maybe x -> Err x
    n x = note ("Undefined " ++ show k ++ ": " ++ v) x

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
  validate (InstanceEx x) = typecheckPresentation (schema x) (pres x)
  eval = evalInstance
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
  validate (QueryEx _) = undefined -- typecheckQuery x
  eval = undefined -- evalQuery
  getOptions = undefined -- getOptionsQuery

evalAqlProgram :: [(String,Kind)] -> Prog -> Env -> Err Env
evalAqlProgram [] _ env = pure env
evalAqlProgram ((v,k):l) prog env = do
  e <- getKindCtx prog v k
  ops <- toOptions (other env) $ getOptions' e
  let to = iOps ops Timeout
  t <- wrapError ("Eval Error in " ++ v) $ timeout' to $ eval' prog env e
  evalAqlProgram l prog $ setEnv env v t

data Graph a = Graph { vertices :: [a], edges :: [(a, a)] } deriving Show

removeEdge :: (Eq a) => (a, a) -> Graph a -> Graph a
removeEdge x (Graph v e) = Graph v (filter (/=x) e)

connections :: (Eq a) => ((a, a) -> a) -> a -> Graph a -> [(a, a)]
connections f0 x (Graph _ e) = filter ((==x) . f0) e

outbound :: Eq b => b -> Graph b -> [(b, b)]
outbound a = connections fst a

inbound :: Eq a => a -> Graph a -> [(a, a)]
inbound a = connections snd a

tsort :: (Eq a) => Graph a -> Err [a]
tsort graph  = tsort' [] (noInbound graph) graph
  where
    noInbound (Graph v e) = filter (flip notElem $ fmap snd e) v
    tsort' l []    (Graph _ []) = pure $ reverse l
    tsort' _ []    _            = Left "There is at least one cycle in the AQL dependency graph."
    tsort' l (n:s) g            = tsort' (n:l) s' g'
      where
        outEdges = outbound n g
        outNodes = snd <$> outEdges
        g'       = foldr removeEdge g outEdges
        s'       = s ++ filter (null . flip inbound g') outNodes

findOrder :: Prog -> Err [(String, Kind)]
findOrder (p@(KindCtx t s i m q tr _)) = do
  ret <- tsort g
  pure $ reverse ret
  where
    g       = Graph (allVars p) $ nub $ f0 t TYPESIDE ++ f0 s SCHEMA ++ f0 i INSTANCE ++ f0 m MAPPING ++ f0 q QUERY ++ f0 tr TRANSFORM
    f0 m0 k = concatMap (\(v,e) -> [ ((v,k),x) | x <- deps e ]) $ Map.toList m0
------------------------------------------------------------------------------------------------------------

evalTypeside :: Prog -> Env -> TypesideExp -> Err TypesideEx
evalTypeside p e (TypesideRaw r) = do
  x <- mapM (evalTypeside p e) $ tsraw_imports r
  evalTypesideRaw (other e) r x
evalTypeside _ env (TypesideVar v) = case Map.lookup v $ typesides env of
  Nothing -> Left $ "Undefined typeside: " ++ show v
  Just (TypesideEx e) -> Right $ TypesideEx e
evalTypeside _ _ TypesideInitial = pure $ TypesideEx $ initialTypeside

convSchema :: (Typeable var1, Typeable ty1, Typeable sym1, Typeable en1, Typeable fk1, Typeable att1,
               Typeable var, Typeable ty, Typeable sym, Typeable en, Typeable fk, Typeable att)
     => Schema var1 ty1 sym1 en1 fk1 att1 -> Schema var ty sym en fk att
convSchema x = fromJust $ cast x

convInstance :: (Typeable var1, Typeable ty1, Typeable sym1, Typeable en1, Typeable fk1, Typeable att1,
               Typeable var, Typeable ty, Typeable sym, Typeable en, Typeable fk, Typeable att,
               Typeable gen, Typeable gen', Typeable sk, Typeable sk', Typeable x, Typeable x', Typeable y, Typeable y')
     => Instance var1 ty1 sym1 en1 fk1 att1 gen' sk' x' y' -> Instance var ty sym en fk att gen sk x y
convInstance x = fromJust $ cast x

evalTransform :: Prog -> Env -> TransformExp -> Err TransformEx
evalTransform _ env (TransformVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ transforms env

evalTransform p env (TransformId s) = do
  (InstanceEx i) <- evalInstance p env s
  pure $ TransformEx $ Transform i i (h i) (g i)
  where
    h i = foldr (\(gen,_) m -> Map.insert gen (Gen gen) m) Map.empty $ Map.toList $ I.gens $ pres i
    g i = foldr (\(sk ,_) m -> Map.insert sk  (Sk  sk)  m) Map.empty $ Map.toList $ I.sks  $ pres i

evalTransform p env (TransformComp f g) = do
  (TransformEx (f' :: Transform var ty sym en fk att gen sk x y gen' sk' x' y')) <- evalTransform p env f
  (TransformEx (g' :: Transform var2 ty2 sym2 en2 fk2 att2 gen2 sk2 x2 y2 gen'2 sk'2 x'2 y'2)) <- evalTransform p env g
  z <- composeTransform f' $ (fromJust $ ((cast g') :: Maybe (Transform var ty sym en fk att gen' sk' x' y' gen'2 sk'2 x'2 y'2)))
  pure $ TransformEx z

evalTransform p env (TransformRaw r) = do
  s0 <- evalInstance p env $ transraw_src r
  s1 <- evalInstance p env $ transraw_dst r
  is <- mapM (evalTransform p env) $ transraw_imports r
  case s0 of
    InstanceEx s -> case s1 of
      InstanceEx (t :: Instance var ty sym en fk att gen sk x y) ->
        evalTransformRaw ((convInstance s)::Instance var ty sym en fk att gen sk x y) t r is

evalTransform prog env (TransformSigma f' i o) = do
  (MappingEx (f'' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping prog env f'
  (TransformEx (i' :: Transform var'' ty'' sym'' en'' fk'' att'' gen sk x y gen' sk' x' y')) <- evalTransform prog env i
  o' <- toOptions (other env) o
  r <- evalSigmaTrans f'' (fromJust $ ((cast i') :: Maybe (Transform var ty sym en fk att gen sk x y gen' sk' x' y'))) o'
  pure $ TransformEx r

evalTransform prog env (TransformDelta f' i o) = do
  (MappingEx (f'' :: Mapping var ty sym en' fk' att' en fk att)) <- evalMapping prog env f'
  (TransformEx (i' :: Transform var'' ty'' sym'' en'' fk'' att'' gen sk x y gen' sk' x' y')) <- evalTransform prog env i
  o' <- toOptions (other env) o
  r <- evalDeltaTrans f'' (fromJust $ ((cast i') :: Maybe (Transform var ty sym en fk att gen sk x y gen' sk' x' y'))) o'
  pure $ TransformEx r

evalTransform prog env (TransformSigmaDeltaUnit f' i o) = do
  (MappingEx (f'' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping prog env f'
  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk x y)) <- evalInstance prog env i
  o' <- toOptions (other env) o
  r <- evalDeltaSigmaUnit f'' (fromJust $ ((cast i') :: Maybe (Instance var ty sym en fk att gen sk x y))) o'
  pure $ TransformEx r

evalTransform prog env (TransformSigmaDeltaCoUnit f' i o) = do
  (MappingEx (f'' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping prog env f'
  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk x y)) <- evalInstance prog env i
  o' <- toOptions (other env) o
  r <- evalDeltaSigmaCoUnit f'' (fromJust $ ((cast i') :: Maybe (Instance var ty sym en' fk' att' gen sk x y))) o'
  pure $ TransformEx r

evalTransform _ _ _ = undefined


evalMapping :: Prog -> Env -> MappingExp -> Err MappingEx
evalMapping _ env (MappingVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ mappings env
evalMapping p env (MappingComp f g) = do
  (MappingEx (f' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping p env f
  (MappingEx (g' :: Mapping var2 ty2 sym2 en2 fk2 att2 en'2 fk'2 att'2)) <- evalMapping p env g
  z <- composeMapping f' $ (fromJust $ ((cast g') :: Maybe (Mapping var ty sym en' fk' att' en'2 fk'2 att'2)))
  pure $ MappingEx z

evalMapping p env (MappingId  s) = do
  (SchemaEx s') <- evalSchema p env s
  pure $ MappingEx $ foldr (\en' (Mapping s'' t e f' a) -> Mapping s'' t (Map.insert en' en' e) (f'' en' s' f') (g' en' s' a)) (Mapping s' s' Map.empty Map.empty Map.empty) (S.ens s')
  where
    f'' en' s' f''' = foldr (\(fk,_) m -> Map.insert fk (Fk  fk $ Var ()) m) f''' $ fksFrom' s' en'
    g'  en' s' f''' = foldr (\(fk,_) m -> Map.insert fk (Att fk $ Var ()) m) f''' $ attsFrom' s' en'

evalMapping p env (MappingRaw r) = do
  s0 <- evalSchema p env $ mapraw_src r
  s1 <- evalSchema p env $ mapraw_dst r
  ix <- mapM (evalMapping p env) $ mapraw_imports r
  case s0 of
    SchemaEx s -> case s1 of
       SchemaEx (t::Schema var ty sym en fk att) ->
         evalMappingRaw ((convSchema s) :: Schema var ty sym en fk att) t r ix

tsToS :: Typeside var ty sym -> Schema var ty sym Void Void Void
tsToS ts'' = Schema ts'' Set.empty Map.empty Map.empty Set.empty Set.empty (\x _ -> absurd x)

evalSchema :: Prog -> Env -> SchemaExp -> Err SchemaEx
evalSchema _ env (SchemaVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ schemas env
evalSchema prog env (SchemaInitial ts) = do
  ts' <- evalTypeside prog env ts
  case ts' of
    TypesideEx ts'' -> pure $ SchemaEx $ tsToS ts''
evalSchema prog env (SchemaRaw r) = do
  t <- evalTypeside prog env $ schraw_ts r
  x <- mapM (evalSchema prog env) $ schraw_imports r
  case t of
    TypesideEx t' -> evalSchemaRaw (other env) t' r x


                                                          
evalSchema _ _ _ = undefined

evalInstance :: Prog -> Env -> InstanceExp -> Either [Char] InstanceEx
evalInstance _ env (InstanceVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ instances env
evalInstance prog env (InstanceInitial s) = do
  ts' <- evalSchema prog env s
  case ts' of
    SchemaEx ts'' -> pure $ InstanceEx $ emptyInstance ts''

evalInstance prog env (InstanceRaw r) = do
  t <- evalSchema prog env $ instraw_schema r
  case t of
    SchemaEx t' -> do
      i <- mapM (evalInstance prog env) (instraw_imports r)
      evalInstanceRaw (other env) t' r i

evalInstance prog env (InstanceSigma f' i o) = do
  (MappingEx (f'' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping prog env f'
  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk x y)) <- evalInstance prog env i
  o' <- toOptions (other env) o
  r <- evalSigmaInst f'' (fromJust $ ((cast i') :: Maybe (Instance var ty sym en fk att gen sk x y))) o'
  return $ InstanceEx r

evalInstance prog env (InstanceDelta f' i o) = do
  (MappingEx (f'' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping prog env f'
  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk x y)) <- evalInstance prog env i
  o' <- toOptions (other env) o
  r <- evalDeltaInst f'' (fromJust $ ((cast i') :: Maybe (Instance var ty sym en' fk' att' gen sk x y))) o'
  return $ InstanceEx r

evalInstance _ _ _ = undefined
