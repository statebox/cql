{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.AQL where

import Prelude hiding (EQ)
import Data.Set as Set
import Data.Map.Strict as Map
import Language.Common as C
import Language.Term as Term
import Language.Schema as S
import Language.Instance as I
import Language.Mapping as M
import Language.Typeside as T
import Language.Transform as Tr
import Language.Query as Q
import           Data.List                  (foldl')
import           Data.Maybe
import           Text.Megaparsec
import           Data.List.NonEmpty 
import Language.Parser (parseAqlProgram)
import Language.Program as P
import Data.Void
import Data.Typeable

-- simple three phase evaluation and reporting
runProg :: String -> Err (Prog, Types, Env)
runProg p = do p1 <- parseAqlProgram p
               o  <- findOrder p1
               p2 <- typecheckAqlProgram o p1
               p3 <- evalAqlProgram o p1 newEnv
               return (p1, p2, p3)
         
--todo: store exception info in other field
type Env = KindCtx TypesideEx SchemaEx InstanceEx MappingEx QueryEx TransformEx ()

wrapError s e = case e of
  Left s' -> Left $ s ++ ": " ++ s'
  Right r -> Right r

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


typecheckTransExp :: Prog -> TransformExp -> Err (InstanceExp, InstanceExp) 
typecheckTransExp p (TransformVar v) = do t <- note ("Undefined transform: " ++ show v) $ Map.lookup v $ transforms p
                                          typecheckTransExp p t  
typecheckTransExp p (TransformId s) = pure (s, s)
typecheckTransExp p (TransformRaw r) = do l' <- typecheckInstExp p $ transraw_src r
                                          r' <- typecheckInstExp p $ transraw_dst r
                                          if   l' == r' 
                                          then pure $ (transraw_src r, transraw_src r)
                                          else Left "Mapping has non equal schemas"

typecheckMapExp :: Prog -> MappingExp -> Err (SchemaExp, SchemaExp) 
typecheckMapExp p (MappingVar v) = do t <- note ("Undefined mapping: " ++ show v) $ Map.lookup v $ mappings p
                                      typecheckMapExp p t  
typecheckMapExp p (MappingId s) = pure (s, s)
typecheckMapExp p (MappingRaw r) = do l' <- typecheckSchemaExp p $ mapraw_src r
                                      r' <- typecheckSchemaExp p $ mapraw_dst r
                                      if   l' == r' 
                                      then pure $ (mapraw_src r, mapraw_dst r)
                                      else Left "Mapping has non equal typesides"



typecheckInstExp :: Prog -> InstanceExp -> Err SchemaExp 
typecheckInstExp p (InstanceVar v) = do t <- note ("Undefined instance: " ++ show v) $ Map.lookup v $ instances p
                                        typecheckInstExp p t  
typecheckInstExp p (InstanceInitial s) = pure s
typecheckInstExp p (InstanceRaw r) = pure $ instraw_schema r

typecheckTypesideExp :: Prog -> TypesideExp -> Err TypesideExp
typecheckTypesideExp p (TypesideVar v) = do t <- note ("Undefined typeside: " ++ show v) $ Map.lookup v $ typesides p
                                            typecheckTypesideExp p t  
typecheckTypesideExp p TypesideInitial = pure TypesideInitial
typecheckTypesideExp p (TypesideRaw r) = pure $ TypesideRaw r

typecheckSchemaExp p (SchemaRaw r) = pure $ schraw_ts r
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
                                              evalAqlProgram l prog $ env { typesides = Map.insert v t $ typesides env }
evalAqlProgram ((v,SCHEMA):l) prog env = do t <- wrapError ("Eval Error in " ++ v) $ evalSchema prog env $ lookup2 v (schemas prog) 
                                            evalAqlProgram l prog $ env { schemas = Map.insert v t $ schemas env }
evalAqlProgram ((v,INSTANCE):l) prog env = do t <- wrapError ("Eval Error in " ++ v) $ evalInstance prog env $ lookup2 v (instances prog) 
                                              evalAqlProgram l prog $ env { instances = Map.insert v t $ instances env }
evalAqlProgram ((v,MAPPING):l) prog env = do t <- wrapError ("Eval Error in " ++ v) $ evalMapping prog env $ lookup2 v (mappings prog) 
                                             evalAqlProgram l prog $ env { mappings = Map.insert v t $ mappings env }
evalAqlProgram ((v,TRANSFORM):l) prog env = do t <- wrapError ("Eval Error in " ++ v) $ evalTransform prog env $ lookup2 v (transforms prog) 
                                               evalAqlProgram l prog $ env { transforms = Map.insert v t $ transforms env }
 
--todo: check acyclic with Data.Graph.DAG

evalAqlProgram _ _ _ = undefined

findOrder :: Prog -> Err [(String, Kind)]
findOrder p = pure $ other p --todo: for now

------------------------------------------------------------------------------------------------------------
 
evalTypeside :: Prog -> Env -> TypesideExp -> Err TypesideEx
evalTypeside _ _ (TypesideRaw r) = evalTypesideRaw r
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
evalTransform p env (TransformVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ transforms env
evalTransform p env (TransformId s) = do (InstanceEx i) <- evalInstance p env s
                                         return $ TransformEx $ Transform i i (h i) (g i)
 where h i  = Prelude.foldr (\(gen,_) m -> Map.insert gen (Gen gen) m) Map.empty $ Map.toList $ I.gens $ pres i
       g i  = Prelude.foldr (\(sk,_) m -> Map.insert sk (Sk sk) m) Map.empty $ Map.toList $ I.sks $ pres i
      
evalTransform p env (TransformRaw r) = do s0 <- evalInstance p env $ transraw_src r 
                                          s1 <- evalInstance p env $ transraw_dst r
                                          case s0 of 
                                           InstanceEx s -> case s1 of 
                                            InstanceEx (t :: Instance var ty sym en fk att gen sk x y) -> 
                                             evalTransformRaw ((convInstance s)::Instance var ty sym en fk att gen sk x y) t r --ok bc typecheck says same ts 


evalMapping :: Prog -> Env -> MappingExp -> Err MappingEx 
evalMapping p env (MappingVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ mappings env
evalMapping p env (MappingId s) = do (SchemaEx s') <- evalSchema p env s
                                     return $ MappingEx $ Prelude.foldr (\en (Mapping s t e f a) -> Mapping s t (Map.insert en en e) (f' en s' f) (g' en s' a)) (Mapping s' s' Map.empty Map.empty Map.empty) (S.ens s') 
 where f' en s' f = Prelude.foldr (\(fk,_) m -> Map.insert fk (Var ()) m) f $ fksFrom' s' en
       g' en s' f = Prelude.foldr (\(fk,_) m -> Map.insert fk (Var ()) m) f $ attsFrom' s' en
 
evalMapping p env (MappingRaw r) = do s0 <- evalSchema p env $ mapraw_src r 
                                      s1 <- evalSchema p env $ mapraw_dst r
                                      case s0 of 
                                        SchemaEx s -> case s1 of 
                                           SchemaEx (t::Schema var ty sym en fk att) -> 
                                             evalMappingRaw ((convSchema s) :: Schema var ty sym en fk att) t r --ok bc typecheck says same ts 
                                       

f :: Typeside var ty sym -> Schema var ty sym Void Void Void
f ts'' = Schema ts'' Set.empty Map.empty Map.empty Set.empty Set.empty undefined

evalSchema :: Prog -> Env -> SchemaExp -> Err SchemaEx
evalSchema _ env (SchemaVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ schemas env
evalSchema prog env (SchemaInitial ts) = do ts' <- evalTypeside prog env ts
                                            case ts' of
                                             TypesideEx ts'' ->
                                               pure $ SchemaEx $ f ts''  
evalSchema prog env (SchemaRaw r) = do t <- evalTypeside prog env $ schraw_ts r 
                                       case t of
                                        TypesideEx t' -> do l <- evalSchemaRaw t' r 
                                                            pure $ l

evalInstance :: Prog -> KindCtx TypesideEx SchemaEx InstanceEx MappingEx QueryEx TransformEx () -> InstanceExp -> Either [Char] InstanceEx
evalInstance _ env (InstanceVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ instances env
evalInstance prog env (InstanceInitial s) = do ts' <- evalSchema prog env s
                                               case ts' of
                                                 SchemaEx ts'' -> pure $ InstanceEx $ emptyInstance ts''

evalInstance prog env (InstanceRaw r) = do t <- evalSchema prog env $ instraw_schema r 
                                           case t of
                                            SchemaEx t' -> do l <- evalInstanceRaw t' r 
                                                              pure $ l

evalInstance _ _ _ = undefined

