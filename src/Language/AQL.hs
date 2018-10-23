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

-- simple three phase evaluation and reporting
runProg :: String -> Err (Prog, Types, Env)
runProg p = do
  p1 <- parseAqlProgram p
  o  <- findOrder p1
  p2 <- typecheckAqlProgram o p1
  p3 <- evalAqlProgram o p1 newEnv
  return (p1, p2, p3)

--todo: store exception info in other field
type Env = KindCtx TypesideEx SchemaEx InstanceEx MappingEx QueryEx TransformEx ()

wrapError :: String -> Either String b -> Either String b
wrapError prefix se = (\s -> prefix ++ ": " ++ s) `left` se

-- type Types = KindCtx () TypesideExp SchemaExp (SchemaExp,SchemaExp) (SchemaExp,SchemaExp) (InstanceExp,InstanceExp) ()

-- some ordering - could be program order, but not necessarily
-- todo: could be backwards, will check w/ mappings, queries
typecheckAqlProgram :: [(String,Kind)] -> Prog -> Err Types
typecheckAqlProgram [] _ = pure newTypes
typecheckAqlProgram ((v,TYPESIDE):l) prog = do t <- wrapError ("Type Error in " ++ v) $ typecheckTypesideExp prog $ lookup2 v (typesides prog)
                                               x <- typecheckAqlProgram l prog
                                               return $ x { typesides = Map.insert v t $ typesides x }
typecheckAqlProgram ((v,SCHEMA):l) prog = do t <- wrapError ("Type Error in " ++ v) $ typecheckSchemaExp prog $ lookup2 v (schemas prog)
                                             x <- typecheckAqlProgram l prog
                                             return $ x { schemas = Map.insert v t $ schemas x }
typecheckAqlProgram ((v,INSTANCE):l) prog = do t <- wrapError ("Type Error in " ++ v) $ typecheckInstExp prog $ lookup2 v (instances prog)
                                               x <- typecheckAqlProgram l prog
                                               return $ x { instances = Map.insert v t $ instances x }
typecheckAqlProgram ((v,MAPPING):l) prog = do t <- wrapError ("Type Error in " ++ v) $ typecheckMapExp prog $ lookup2 v (mappings prog)
                                              x <- typecheckAqlProgram l prog
                                              return $ x { mappings = Map.insert v t $ mappings x }

typecheckAqlProgram ((v,TRANSFORM):l) prog = do t <- wrapError ("Type Error in " ++ v) $ typecheckTransExp prog $ lookup2 v (transforms prog)
                                                x <- typecheckAqlProgram l prog
                                                return $ x { transforms = Map.insert v t $ transforms x }
typecheckAqlProgram _ _ = undefined


typecheckTransExp :: Prog -> TransformExp -> Err (InstanceExp, InstanceExp)
typecheckTransExp p (TransformVar v) = do t <- note ("Undefined transform: " ++ show v) $ Map.lookup v $ transforms p
                                          typecheckTransExp p t
typecheckTransExp _ (TransformId s) = pure (s, s)
typecheckTransExp p (TransformSigma f' h o) = do (s,_) <- typecheckMapExp p f'
                                                 (i,j) <- typecheckTransExp p h
                                                 s' <- typecheckInstExp p i
                                                 if s == s'
                                                 then pure (InstanceSigma f' i o, InstanceSigma f' j o)
                                                 else Left $ "Source of mapping does not match instance schema"
typecheckTransExp p (TransformSigmaDeltaUnit f' i o) = do (s,_) <- typecheckMapExp p f'
                                                          x <- typecheckInstExp p i
                                                          if s == x
                                                          then pure (i, InstanceDelta f' (InstanceSigma f' i o) o)
                                                          else Left $ "Source of mapping does not match instance schema"
typecheckTransExp p (TransformSigmaDeltaCoUnit f' i o) = do (_,t) <- typecheckMapExp p f'
                                                            x <- typecheckInstExp p i
                                                            if t == x
                                                            then pure (i, InstanceSigma f' (InstanceDelta f' i o) o)
                                                            else Left $ "Target of mapping does not match instance schema"

typecheckTransExp p (TransformDelta f' h o) = do (_,t) <- typecheckMapExp p f'
                                                 (i,j) <- typecheckTransExp p h
                                                 t' <- typecheckInstExp p i
                                                 if t == t'
                                                 then pure (InstanceDelta f' i o, InstanceDelta f' j o)
                                                 else Left $ "Target of mapping does not match instance schema"

typecheckTransExp p (TransformRaw r) = do l' <- typecheckInstExp p $ transraw_src r
                                          r' <- typecheckInstExp p $ transraw_dst r
                                          if   l' == r'
                                          then pure $ (transraw_src r, transraw_src r)
                                          else Left "Mapping has non equal schemas"
typecheckTransExp _ _ = undefined

typecheckMapExp :: Prog -> MappingExp -> Err (SchemaExp, SchemaExp)
typecheckMapExp p (MappingVar v) = do t <- note ("Undefined mapping: " ++ show v) $ Map.lookup v $ mappings p
                                      typecheckMapExp p t
typecheckMapExp _ (MappingId s) = pure (s, s)
typecheckMapExp p (MappingRaw r) = do l' <- typecheckSchemaExp p $ mapraw_src r
                                      r' <- typecheckSchemaExp p $ mapraw_dst r
                                      if   l' == r'
                                      then pure $ (mapraw_src r, mapraw_dst r)
                                      else Left "Mapping has non equal typesides"



typecheckInstExp :: Prog -> InstanceExp -> Err SchemaExp
typecheckInstExp p (InstanceVar v) = do t <- note ("Undefined instance: " ++ show v) $ Map.lookup v $ instances p
                                        typecheckInstExp p t
typecheckInstExp _ (InstanceInitial s) = pure s
typecheckInstExp _ (InstanceRaw r) = pure $ instraw_schema r
typecheckInstExp p (InstanceSigma f' i _) = do  (s,t) <- typecheckMapExp p f'
                                                s' <- typecheckInstExp p i
                                                if s == s'
                                                then pure t
                                                else Left "(Sigma): Instance not on mapping source."
typecheckInstExp p (InstanceDelta f' i _) = do  (s,t) <- typecheckMapExp p f'
                                                t' <- typecheckInstExp p i
                                                if t == t'
                                                then pure s
                                                else Left "(Delta): Instance not on mapping target."

typecheckInstExp _ _ = undefined

typecheckTypesideExp :: Prog -> TypesideExp -> Err TypesideExp
typecheckTypesideExp p (TypesideVar v) = do t <- note ("Undefined typeside: " ++ show v) $ Map.lookup v $ typesides p
                                            typecheckTypesideExp p t
typecheckTypesideExp _ TypesideInitial = pure TypesideInitial
typecheckTypesideExp _ (TypesideRaw r) = pure $ TypesideRaw r

typecheckSchemaExp
  :: KindCtx TypesideExp SchemaExp InstanceExp MappingExp QueryExp TransformExp [(String, Kind)]
  -> SchemaExp
  -> Either String TypesideExp
typecheckSchemaExp _ (SchemaRaw r) = pure $ schraw_ts r
typecheckSchemaExp p (SchemaVar v) = do t <- note ("Undefined schema: " ++ show v) $ Map.lookup v $ schemas p
                                        typecheckSchemaExp p t
typecheckSchemaExp p (SchemaInitial t) = do _ <- typecheckTypesideExp p t
                                            return t
typecheckSchemaExp p (SchemaCoProd l r) = do l' <- typecheckSchemaExp p l
                                             r' <- typecheckSchemaExp p r
                                             if l' == r'
                                             then return l'
                                             else Left "Coproduct has non equal typesides"

evalAqlProgram :: [(String,Kind)] -> Prog -> Env -> Err Env
evalAqlProgram [] _ e = pure e
evalAqlProgram ((v,TYPESIDE):l) prog env = do t <- wrapError ("Eval Error in " ++ v) $ evalTypeside prog env $ lookup2 v (typesides prog)
                                              _ <- case t of
                                                     TypesideEx x -> typecheckTypeside x
                                              evalAqlProgram l prog $ env { typesides = Map.insert v t $ typesides env }
evalAqlProgram ((v,SCHEMA):l) prog env = do t <- wrapError ("Eval Error in " ++ v) $ evalSchema prog env $ lookup2 v (schemas prog)
                                            _ <- case t of
                                                     SchemaEx x -> typecheckSchema x
                                            evalAqlProgram l prog $ env { schemas = Map.insert v t $ schemas env }
evalAqlProgram ((v,INSTANCE):l) prog env = do t <- wrapError ("Eval Error in " ++ v) $ evalInstance prog env $ lookup2 v (instances prog)
                                              _ <- case t of
                                                     InstanceEx i -> do {_ <- typecheckPresentation (schema i) (pres i); checkSatisfaction i}
                                              evalAqlProgram l prog $ env { instances = Map.insert v t $ instances env }
evalAqlProgram ((v,MAPPING):l) prog env = do t <- wrapError ("Eval Error in " ++ v) $ evalMapping prog env $ lookup2 v (mappings prog)
                                             _ <- case t of
                                                     MappingEx i -> do {_ <- typecheckMapping i; validateMapping i}
                                             evalAqlProgram l prog $ env { mappings = Map.insert v t $ mappings env }
evalAqlProgram ((v,TRANSFORM):l) prog env = do t <- wrapError ("Eval Error in " ++ v) $ evalTransform prog env $ lookup2 v (transforms prog)
                                               _ <- case t of
                                                     TransformEx i -> do {_ <- typecheckTransform i; validateTransform i}
                                               evalAqlProgram l prog $ env { transforms = Map.insert v t $ transforms env }
evalAqlProgram _ _ _ = undefined

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
findOrder (KindCtx t s i m q tr o) = do
  ret <- tsort g
  pure $ reverse ret
  where
    g       = Graph o $ nub $ f0 t TYPESIDE ++ f0 s SCHEMA ++ f0 i INSTANCE ++ f0 m MAPPING ++ f0 q QUERY ++ f0 tr TRANSFORM
    f0 m0 k = concatMap (\(v,e) -> [ ((v,k),x) | x <- deps e ]) $ Map.toList m0
------------------------------------------------------------------------------------------------------------

evalTypeside :: Prog -> Env -> TypesideExp -> Err TypesideEx
evalTypeside p e (TypesideRaw r) = do x <- mapM (evalTypeside p e) $ tsraw_imports r
                                      evalTypesideRaw r x
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
  o' <- toOptions o
  r <- evalSigmaTrans f'' (fromJust $ ((cast i') :: Maybe (Transform var ty sym en fk att gen sk x y gen' sk' x' y'))) o'
  pure $ TransformEx r
evalTransform prog env (TransformDelta f' i o) = do
  (MappingEx (f'' :: Mapping var ty sym en' fk' att' en fk att)) <- evalMapping prog env f'
  (TransformEx (i' :: Transform var'' ty'' sym'' en'' fk'' att'' gen sk x y gen' sk' x' y')) <- evalTransform prog env i
  o' <- toOptions o
  r <- evalDeltaTrans f'' (fromJust $ ((cast i') :: Maybe (Transform var ty sym en fk att gen sk x y gen' sk' x' y'))) o'
  pure $ TransformEx r
evalTransform prog env (TransformSigmaDeltaUnit f' i o) = do
  (MappingEx (f'' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping prog env f'
  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk x y)) <- evalInstance prog env i
  o' <- toOptions o
  r <- evalDeltaSigmaUnit f'' (fromJust $ ((cast i') :: Maybe (Instance var ty sym en fk att gen sk x y))) o'
  pure $ TransformEx r
evalTransform prog env (TransformSigmaDeltaCoUnit f' i o) = do
  (MappingEx (f'' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping prog env f'
  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk x y)) <- evalInstance prog env i
  o' <- toOptions o
  r <- evalDeltaSigmaCoUnit f'' (fromJust $ ((cast i') :: Maybe (Instance var ty sym en' fk' att' gen sk x y))) o'
  pure $ TransformEx r

evalTransform _ _ _ = undefined


evalMapping :: Prog -> Env -> MappingExp -> Err MappingEx
evalMapping _ env (MappingVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ mappings env
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

f :: Typeside var ty sym -> Schema var ty sym Void Void Void
f ts'' = Schema ts'' Set.empty Map.empty Map.empty Set.empty Set.empty (\x _ -> absurd x)

evalSchema :: Prog -> Env -> SchemaExp -> Err SchemaEx
evalSchema _ env (SchemaVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ schemas env
evalSchema prog env (SchemaInitial ts) = do ts' <- evalTypeside prog env ts
                                            case ts' of
                                             TypesideEx ts'' ->
                                               pure $ SchemaEx $ f ts''
evalSchema prog env (SchemaRaw r) = do t <- evalTypeside prog env $ schraw_ts r
                                       x <- mapM (evalSchema prog env) $ schraw_imports r
                                       case t of
                                        TypesideEx t' -> do l <- evalSchemaRaw t' r x
                                                            pure $ l
evalSchema _ _ _ = undefined

evalInstance :: Prog -> KindCtx TypesideEx SchemaEx InstanceEx MappingEx QueryEx TransformEx () -> InstanceExp -> Either [Char] InstanceEx
evalInstance _ env (InstanceVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ instances env
evalInstance prog env (InstanceInitial s) = do ts' <- evalSchema prog env s
                                               case ts' of
                                                 SchemaEx ts'' -> pure $ InstanceEx $ emptyInstance ts''

evalInstance prog env (InstanceRaw r) = do t <- evalSchema prog env $ instraw_schema r
                                           case t of
                                            SchemaEx t' -> do i <- mapM (evalInstance prog env) (instraw_imports r)
                                                              l <- evalInstanceRaw t' r i
                                                              pure $ l
evalInstance prog env (InstanceSigma f' i o) = do (MappingEx (f'' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping prog env f'
                                                  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk x y)) <- evalInstance prog env i
                                                  o' <- toOptions o
                                                  r <- evalSigmaInst f'' (fromJust $ ((cast i') :: Maybe (Instance var ty sym en fk att gen sk x y))) o'
                                                  return $ InstanceEx r
evalInstance prog env (InstanceDelta f' i o) = do (MappingEx (f'' :: Mapping var ty sym en fk att en' fk' att')) <- evalMapping prog env f'
                                                  (InstanceEx (i' :: Instance var'' ty'' sym'' en'' fk'' att'' gen sk x y)) <- evalInstance prog env i
                                                  o' <- toOptions o
                                                  r <- evalDeltaInst f'' (fromJust $ ((cast i') :: Maybe (Instance var ty sym en' fk' att' gen sk x y))) o'
                                                  return $ InstanceEx r

evalInstance _ _ _ = undefined
