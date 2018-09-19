{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies #-}

module Language.Term where

import Prelude hiding (EQ)
import Data.Set as Set
import Data.Map.Strict as Map
import Data.List (intercalate)
import Language.Common

data Term var ty sym en fk att gen sk
  = Var var
  | Sym sym  [Term var ty sym en fk att gen sk]
  | Fk  fk   (Term var ty sym en fk att gen sk)
  | Att att  (Term var ty sym en fk att gen sk)
  | Gen gen
  | Sk  sk

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) =>
  Show (Term var ty sym en fk att gen sk)
  where
    show x = case x of
     Var v      -> show v
     Gen g      -> show g
     Sk  s      -> show s
     Fk  fk  a  -> show a ++ "." ++ show fk
     Att att a  -> show a ++ "." ++ show att
     Sym sym az -> show sym ++ "(" ++ (intercalate "," . fmap show $ az) ++ ")"

deriving instance (Eq var, Eq sym, Eq fk, Eq att, Eq gen, Eq sk) => Eq (Term var ty sym en fk att gen sk)

deriving instance (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk) => Ord (Term var ty sym en fk att gen sk)

-- TODO wrap Map class to throw an error (or do something less ad hoc) if a key is ever put twice
type Ctx k v = Map k v

-- Our own pair type for pretty printing purposes
newtype EQ var ty sym en fk att gen sk
  = EQ (Term var ty sym en fk att gen sk, Term var ty sym en fk att gen sk) deriving (Ord,Eq)

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) => Show (EQ var ty sym en fk att gen sk) where
  show (EQ (lhs,rhs)) = show lhs ++ " = " ++ show rhs

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

-- TODO
--data Err1 t
--  = CannotFindVar t
--  | Undefined t

-- I've given up on non string based error handling for now
typeOf'
  :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> Ctx var (ty + en)
  -> Term    var ty sym en fk att gen sk
  -> Err (ty + en)
typeOf' _ ctx (Var v) = note ("Unbound variable: " ++ show v) $ Map.lookup v ctx
typeOf' col _ (Gen g) = case Map.lookup g $ cgens col of
  Nothing -> Left $ "Unknown generator: " ++ show g
  Just t -> pure $ Right t
typeOf' col _ (Sk s) = case Map.lookup s $ csks col of
  Nothing -> Left $ "Unknown labelled null: " ++ show s
  Just t -> pure $ Left t
typeOf' col ctx (Fk f a) = case Map.lookup f $ cfks col of
  Nothing -> Left $ "Unknown foreign key: " ++ show f
  Just (s, t) -> do s' <- typeOf' col ctx a
                    if (Right s) == s' then pure $ Right t else Left $ "Expected argument to have entity " ++
                     show s ++ " but given " ++ show s'
typeOf' col ctx (Att f a) = case Map.lookup f $ catts col of
  Nothing -> Left $ "Unknown attribute: " ++ show f
  Just (s, t) -> do s' <- typeOf' col ctx a
                    if (Right s) == s' then pure $ Left t else Left $ "Expected argument to have entity " ++
                     show s ++ " but given " ++ show s'
typeOf' col ctx (Sym f a) = case Map.lookup f $ csyms col of
  Nothing -> Left $ "Unknown function symbol: " ++ show f
  Just (s, t) -> do s' <- mapM (typeOf' col ctx) a
                    if length s' == length s
                    then if (fmap Left s) == s'
                         then pure $ Left t
                         else Left $ "Expected arguments to have types " ++
                     show s ++ " but given " ++ show s'
                    else Left $ "Expected argument to have arity " ++
                     show (length s) ++ " but given " ++ show (length s')

typeOfEq'
  :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> (Ctx var (ty + en), EQ var ty sym en fk att gen sk)
  -> Err (ty + en)
typeOfEq' col (ctx, EQ (lhs, rhs)) = do lhs' <- typeOf' col ctx lhs
                                        rhs' <- typeOf' col ctx rhs
                                        if lhs' == rhs'
                                        then pure lhs'
                                        else Left $ "Equation lhs has type " ++ show lhs' ++ " but rhs has type " ++ show rhs'

checkDoms :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> Err ()
checkDoms col = do
  _ <- mapM f $ Map.elems $ csyms col
  _ <- mapM g $ Map.elems $ cfks  col
  _ <- mapM h $ Map.elems $ catts col
  _ <- mapM isEn $ Map.elems $ cgens col
  _ <- mapM isTy $ Map.elems $ csks  col
  pure ()
 where f (t1,t2) = do _ <- mapM isTy t1
                      isTy t2
       g (e1,e2) = do isEn e1
                      isEn e2
       h (e,t) = do isEn e
                    isTy t
       isEn x = if Set.member x $ cens col
                then pure ()
                else Left $ "Not an entity: " ++ show x
       isTy x = if Set.member x $ ctys col
                then pure ()
                else Left $ "Not a type: " ++ show x


typeOfCol
  :: (Ord var, Show var, Ord gen, Show gen, Ord sk, Show sk, Ord fk, Show fk, Ord en, Show en, Show ty, Ord ty, Show att, Ord att, Show sym, Ord sym)
  => Collage var ty sym en fk att gen sk
  -> Err ()
typeOfCol col = do checkDoms col
                   _ <- mapM (typeOfEq' col) $ Set.toList $ ceqs col
                   pure ()


data RawTerm = RawApp String [RawTerm]
 deriving Eq

instance Show RawTerm where
 show (RawApp sym az) = show sym ++ "(" ++ (intercalate "," . fmap show $ az) ++ ")"


--Set is not Traversable! Lame
