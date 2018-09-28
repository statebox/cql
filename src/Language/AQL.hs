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
               _ <- validateAqlProgram o p1
               p3 <- evalAqlProgram o p1 newEnv
               return (p1, p2, p3)



-- kinds ---------------

-- todo: raw string based syntax with type inference, etc


--todo: store exception info in other field
type Env = KindCtx TypesideEx SchemaEx InstanceEx MappingEx QueryEx TransformEx ()



-- some ordering - could be program order, but not necessarily
typecheckAqlProgram :: [(String,Kind)] -> Prog -> Err Types
typecheckAqlProgram [] _ = pure newTypes
typecheckAqlProgram ((v,TYPESIDE):l) prog = do _ <- note ("Undefined AQL typeside: " ++ show v) $ Map.lookup v $ typesides prog
                                               typecheckAqlProgram l prog
typecheckAqlProgram _ _ = undefined

validateAqlProgram :: [(String,Kind)] -> Prog -> Err ()
validateAqlProgram [] _ = pure ()
validateAqlProgram ((v,TYPESIDE):l) prog =  do _ <- validate' $ lookup' v $ typesides prog
                                               validateAqlProgram l prog
validateAqlProgram _ _ = undefined

validate' :: a
validate' = undefined
 
--todo: check acyclic with Data.Graph.DAG
evalAqlProgram :: [(String,Kind)] -> Prog -> Env -> Err Env
evalAqlProgram [] _ env = pure env
evalAqlProgram ((v,TYPESIDE):l) prog env = case lookup' v $ typesides env of
                                               TypesideEx ts2 -> let ts' = Map.insert v (TypesideEx ts2) $ typesides env  in
                                                                     evalAqlProgram l prog $ env { typesides = ts' }
evalAqlProgram _ _ _ = undefined

findOrder :: Prog -> Err [(String, Kind)]
findOrder p = pure $ other p --todo: for now

-----------
----------------------------------------------------------------------------------------------------------------------

 
evalTypeside :: Prog -> Env -> TypesideExp -> Err TypesideEx
evalTypeside _ _ (TypesideRaw r) = evalTypesideRaw r
evalTypeside _ env (TypesideVar v) = case Map.lookup v $ typesides env of
  Nothing -> Left $ "Undefined typeside: " ++ show v
  Just (TypesideEx e) -> Right $ TypesideEx e
-- evalTypeside _ _ TypesideInitial = pure $ TypesideEx $ Typeside Set.empty Map.empty Set.empty undefined -- todo: replace undefined with non effectful code

evalInstance :: Prog -> KindCtx TypesideEx SchemaEx InstanceEx MappingEx QueryEx TransformEx () -> InstanceExp -> Either [Char] InstanceEx
evalInstance _ env (InstanceVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ instances env
evalInstance prog env (InstanceInitial s) = do ts' <- evalSchema prog env s
                                               case ts' of
                                                 SchemaEx ts'' -> undefined 
                                            --      pure $ InstanceEx $ Instance ts''
                                            --             (Presentation Map.empty Map.empty Set.empty) undefined $ Algebra ts''
                                             --           undefined undefined undefined undefined undefined undefined 
                                             --           undefined 
evalInstance _ _ _ = undefined


f :: Typeside var ty sym -> Schema var ty sym Void Void Void
f ts'' = Schema ts'' Set.empty Map.empty Map.empty Set.empty Set.empty undefined

evalSchema :: Prog -> Env -> SchemaExp -> Either [Char] SchemaEx
evalSchema _ env (SchemaVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ schemas env
evalSchema prog env (SchemaInitial ts) = do ts' <- evalTypeside prog env ts
                                            case ts' of
                                             TypesideEx ts'' ->
                                               pure $ SchemaEx $ f ts''  
evalSchema _ _ _ = undefined
--evalSchema ctx (SchemaCoProd s1 s2) = Left "todo"
--todo: additional schema functions

evalTransform :: p -> KindCtx ts s i m q b o -> TransformExp -> Either [Char] b
evalTransform _ env (TransformVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ transforms env
evalTransform _ _ _ = undefined

--------------------------------------------------------------------------------


evalMapping :: p -> KindCtx ts s i b q t o -> MappingExp -> Either [Char] b
evalMapping _ env (MappingVar v) = note ("Could not find " ++ show v ++ " in ctx") $ Map.lookup v $ mappings env
evalMapping _ _ _ = undefined
