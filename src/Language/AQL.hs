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

typecheckInstExp :: Prog -> InstanceExp -> Err SchemaExp 
typecheckInstExp p (InstanceVar v) = do t <- note ("Undefined instance: " ++ show v) $ Map.lookup v $ instances p
                                        typecheckInstExp p t  
typecheckInstExp p (InstanceInitial s) = pure s
typecheckInstExp p (InstanceRaw r) = pure $ instraw_schema r

typecheckTypesideExp :: Prog -> TypesideExp -> Err ()
typecheckTypesideExp p (TypesideVar v) = do t <- note ("Undefined typeside: " ++ show v) $ Map.lookup v $ typesides p
                                            typecheckTypesideExp p t  
typecheckTypesideExp p TypesideInitial = pure ()
typecheckTypesideExp p (TypesideRaw _) = pure ()

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


f :: Typeside var ty sym -> Schema var ty sym Void Void Void
f ts'' = Schema ts'' Set.empty Map.empty Map.empty Set.empty Set.empty undefined

evalSchema :: Prog -> Env -> SchemaExp -> Either String SchemaEx
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
                                                 SchemaEx ts'' -> undefined 
                                            --      pure $ InstanceEx $ Instance ts''
                                            --             (Presentation Map.empty Map.empty Set.empty) undefined $ Algebra ts''
                                             --           undefined undefined undefined undefined undefined undefined 
                                             --           undefined 
evalInstance prog env (InstanceRaw r) = do t <- evalSchema prog env $ instraw_schema r 
                                           case t of
                                            SchemaEx t' -> do l <- evalInstanceRaw t' r 
                                                              pure $ l

evalInstance _ _ _ = undefined

{--
evalTransform :: p -> KindCtx ts s i m q b o -> TransformExp -> Either [Char] b
evalTransform _ env (TransformVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ transforms env
evalTransform _ _ _ = undefined


evalMapping :: p -> KindCtx ts s i b q t o -> MappingExp -> Either [Char] b
evalMapping _ env (MappingVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ mappings env
evalMapping _ _ _ = undefined --}
