{-# LANGUAGE ExistentialQuantification, ExplicitForAll, StandaloneDeriving, DuplicateRecordFields,ScopedTypeVariables,InstanceSigs, KindSignatures, GADTs, FlexibleContexts,StandaloneDeriving, TypeSynonymInstances, FlexibleInstances #-}

module Main where
import Prelude hiding (EQ)  
import Data.Typeable
import Data.Set as Set
import Data.Map.Strict as Map
import Data.Void
import Data.List as List
   

--  Terms and theories --------------------------------------

data Term var ty sym en fk att gen sk where    
 Var :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk,
  Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk)
   => var -> Term var ty sym en fk att gen sk 
 Sym :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk,
  Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) => 
   sym -> [Term var ty sym en fk att gen sk] ->
  Term var ty sym en fk att gen sk
 Fk :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk,
  Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) => 
  fk -> (Term var ty sym en fk att gen sk) -> Term var ty sym en fk att gen sk
 Att :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk,
  Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) =>
  att -> (Term var ty sym en fk att gen sk) -> Term var ty sym en fk att gen sk
 Gen :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk,
  Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) => 
  gen -> Term var ty sym en fk att gen sk 
 Sk :: (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk,
  Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk) => 
  sk -> Term var ty sym en fk att gen sk 
  
instance Show (Term var ty sym en fk att gen sk) where
 show x = case x of
           Var v -> show v
           Gen g -> show g
           Sk  s -> show s
           Fk  fk  a  -> (show a) ++ "." ++ (show fk)
           Att att a  -> (show a) ++ "." ++ (show att)
           Sym sym az -> (show sym) ++ "(" ++ (intercalate "," $ List.map show az) ++ ")" 


deriving instance Eq (Term var ty sym en fk att gen sk)
deriving instance Ord (Term var ty sym en fk att gen sk)

type Ctx k v = Map k v --todo: wrap Map class to throw an error if a key is ever put twice
 
newtype EQ var ty sym en fk att gen sk 
 = EQ (Term var ty sym en fk att gen sk, Term var ty sym en fk att gen sk)
 deriving Eq
 
instance Show (EQ var ty sym en fk att gen sk) where
 show (EQ (lhs,rhs)) = ((show lhs) ++ " = " ++ (show rhs))

data Collage var ty sym en fk att gen sk = Collage {
   ctx  :: Ctx var (Either ty en)
 , eqs  :: EQ var ty sym en fk att gen sk
 , tys  :: Set ty
 , ens  :: Set en
 , fks  :: Map fk (en, en)
 , atts :: Map att (en, ty)
 , gens :: Map gen en
 , sks  :: Map sk ty }
 deriving (Eq, Show)
 
typeOf :: Collage var ty sym en fk att gen sk -> 
  Term var ty sym en fk att gen sk -> Either String (Either ty en)
typeOf col (Var var) = case Map.lookup var (ctx col) of 
    Nothing -> Left $ "Cannot find variable " ++ (show var) ++ " in " ++ (show $ ctx col)  
    Just v  -> return v    
typeOf _ _ = undefined     

--  Semantics -----------------------------------------------------------------

data Typeside var ty sym = Typeside {
  tys :: Set ty
, syms :: Map sym ([ty], ty)
, eqs :: Set (Ctx var ty, EQ var ty sym Void Void Void Void Void)
, eq :: Ctx var ty -> EQ var ty sym Void Void Void Void Void -> Bool                 

  {-- since we're in Haskell, a different DSL embedding strategy might be called for than the java version
, hakell_tys :: Map ty String
, haskell_syms :: Map sym String --}
} 

typesideToCollage :: Typeside var ty sym 
  -> Collage var ty sym Void Void Void Void Void 
typesideToCollage = undefined -- todo  


instance (Eq var, Eq ty, Eq sym) => Eq (Typeside var ty sym) where 
 Typeside tys syms eqs eq == Typeside tys' syms' eqs' eq' =
  (tys == tys') && (syms == syms') && (eqs == eqs')
instance (Show var, Show ty, Show sym) => Show (Typeside var ty sym) where
 show (Typeside tys syms eqs eq) = "tys = " ++ (show tys) ++ 
   "\nsyms = " ++ (show syms) ++ "\neqs = " ++ (show eqs)
 
--example typeside one sort Dom { c0 ,..., c100 }
typesideDom = Typeside (Set.singleton "Dom") sym (Set.empty) (\ctx (EQ (lhs,rhs)) -> lhs == rhs)
 where sym = sym' 100
       sym' 0 = Map.empty 
       sym' n = Map.insert ("c" ++ (show n)) ([], "Dom") $ sym' (n-1)

-------------------

data Schema var ty sym en fk att = Schema {
    typeside :: Typeside var ty sym
  , ens  :: Set en
  , fks  :: Map fk (en, en)
  , atts :: Map att (en, ty)
  , path_eqs :: Set (en, EQ () Void Void en fk Void Void Void)
  , obs_eqs  :: Set (en, EQ () ty sym en fk att Void Void)
  , eq :: en -> EQ () ty sym en fk att Void Void -> Bool
} 

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att)
  => Eq (Schema var ty sym en fk att) where
 Schema ts ens fks atts path_eqs obs_eqs eq ==
  Schema ts' ens' fks' atts' path_eqs' obs_eqs' eq'
   = (ens == ens') && (fks == fks') && (atts == atts')
    && (path_eqs == path_eqs') && (obs_eqs == obs_eqs')
    && (ts == ts')
    
instance (Show var, Show ty, Show sym, Show en, Show fk, Show att)
  => Show (Schema var ty sym en fk att) where
 show (Schema ts ens fks atts path_eqs obs_eqs eq) = 
   "ens = " ++ (show ens) ++ 
   "\nfks = " ++ (show fks) ++ "\natts = " ++ (show atts) ++
   "\npath_eqs = " ++ (show path_eqs) ++ "\nobs_eqs = " ++ (show obs_eqs)

schemaToCollage :: Schema var ty sym en fk att
  -> Collage var ty sym en fk att Void Void
schemaToCollage = undefined -- todo  

schemaOne = Schema typesideDom (Set.singleton "A") Map.empty
 atts' Set.empty Set.empty (\en (EQ (lhs, rhs)) -> lhs == rhs)
 where atts' = Map.insert "A_att" ("A", "Dom") Map.empty

schemaTwo = Schema typesideDom (Set.union (Set.singleton "A") (Set.singleton "B")) (Map.insert "f" ("A", "B") Map.empty) atts' Set.empty Set.empty (\en (EQ (lhs, rhs)) -> lhs == rhs)
  where atts' = Map.insert "A_att" ("A", "Dom") $ Map.insert "B_att" ("B", "Dom") Map.empty

-------------

data Algebra var ty sym en fk att gen sk x y = Algebra {
   schemaA :: Schema var ty sym en fk att 
  
  , ens  :: Map en (Set x)
  , fks  :: Map fk (Map x x)
  , atts :: Map att (Map x (Term Void ty sym Void Void Void Void y))
   
  , nf :: Term Void Void Void en fk Void gen Void -> x
  , repr :: x -> Term Void Void Void en fk Void gen Void
  
  , nf' :: Term var ty sym en fk att gen sk -> 
           Term Void ty sym Void Void Void Void y
         
  , repr' :: Term Void ty sym Void Void Void Void y ->
             Term var ty sym en fk att gen sk
} -- omit Eq, doesn't seem to be necessary 
    
instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y)
  => Show (Algebra var ty sym en fk att gen sk x y) where
 show (Algebra _ ens fks atts nf repr nf' repr') = 
   "ens = " ++ (show ens) ++ 
   "\nfks = " ++ (show fks) ++ "\natts = " ++ (show atts)

data Instance var ty sym en fk att gen sk x y = Instance {
    schema :: Schema var ty sym en fk att 
  , gens :: Map gen en
  , sks :: Map sk ty
  , eqs :: Set (EQ Void ty sym en fk att gen sk)             
  , eq :: EQ var ty sym en fk att gen sk -> Bool
    
  , algebra :: Algebra var ty sym en fk att gen sk x y    

} 

 
instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y)
  => Show (Instance var ty sym en fk att gen sk x y) where
 show (Instance _ gens sks eqs eq _) = 
   "gens = " ++ (show gens) ++ 
   "\nsks = " ++ (show sks) ++ "\neqs = " ++ (show eqs)

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Eq x, Eq y)
  => Eq (Instance var ty sym en fk att gen sk x y) where
 (Instance schema gens sks eqs _ _) == (Instance schema' gens' sks' eqs' _ _)
  = (schema == schema') && (gens == gens') && (sks == sks') && (eqs == eqs') 


validate :: Instance var ty sym en fk att gen sk x y
 -> Algebra var ty sym en fk att gen sk x y -> Either String ()
validate _ _ = Left "todo" --todo


instanceToCollage :: Instance var ty sym en fk att gen sk x y
  -> Collage var ty sym en fk att gen sk
instanceToCollage = undefined -- todo  

instanceOne = Instance schemaOne 
 (Map.insert "g1" "A" Map.empty) Map.empty  Set.empty (\(EQ (lhs,rhs)) -> lhs == rhs)
 $ Algebra schemaOne (Map.fromList [("A", Set.singleton "x")]) 
   (Map.empty) (Map.fromList [("A_att", Map.fromList [("x",Sym "c42" [])])])
   (\t -> "x") (\t -> Gen "g1") (\t -> Sym "c42" []) (\t -> Sym "c42" [])


-------------

data Mapping var ty sym en fk att en' fk' att' = Mapping {
    src :: Schema var ty sym en  fk  att
  , dst :: Schema var ty sym en' fk' att'
  
  , ens  :: Map en  en'
  , fks  :: Map fk  (Term () Void Void en' fk' Void Void Void)
  , atts :: Map att (Term () ty   sym  en' fk' att' Void Void)
} 

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att')
  => Show (Mapping var ty sym en fk att en' fk' att') where
 show (Mapping _ _ ens fks atts) = 
   "ens = " ++ (show ens) ++ 
   "\nfks = " ++ (show fks) ++ "\natts = " ++ (show atts)

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq en', Eq fk', Eq att')
  => Eq (Mapping var ty sym en fk att en' fk' att') where
 (Mapping s1 s2 ens fks atts) == (Mapping s1' s2' ens' fks' atts')
  = (s1 == s1') && (s2 == s2') && (ens == ens') && (fks == fks') && (atts == atts') 


mappingTwoToOne = Mapping schemaTwo schemaOne
 (Map.fromList [("B", "A"), ("A","A")])
 (Map.fromList [("f", Var ())])
 (Map.fromList [("A_att", Att "att" (Var ())), ("B_att", Att "att" (Var ()))])

-----

data Query var ty sym en fk att en' fk' att' = Query {
    srcQ :: Schema var ty sym en fk att
  , dstQ :: Schema var ty sym en' fk' att'
  
  , ens  :: Map en' (Ctx var en, Set (EQ var ty sym en fk att Void Void))
  , fks  :: Map fk'  (Ctx var (Term var Void Void en fk Void Void Void))
  , atts :: Map att' (Term var ty   sym  en fk att  Void Void)
} 

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att')
  => Show (Query var ty sym en fk att en' fk' att') where
 show (Query _ _ ens fks atts) = 
   "ens = " ++ (show ens) ++ 
   "\nfks = " ++ (show fks) ++ "\natts = " ++ (show atts)

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq en', Eq fk', Eq att')
  => Eq (Query var ty sym en fk att en' fk' att') where
 (Query s1 s2 ens fks atts) == (Query s1' s2' ens' fks' atts')
  = (s1 == s1') && (s2 == s2') && (ens == ens') && (fks == fks') && (atts == atts') 


------


data Transform var ty sym en fk att gen sk x y gen' sk' x' y' 
 = Transform { 
    srcT  :: Instance var ty sym en fk att gen sk x y
  , dstT  :: Instance var ty sym en fk att gen' sk' x' y'
  , gens :: Map gen (Term Void Void Void en fk Void gen' Void)
  , sks  :: Map sk  (Term var  ty   sym  en fk att  gen' sk') 
} 


instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show gen, Show sk, Show x, Show y, Show gen', Show sk', Show x', Show y')
  => Show (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
 show (Transform _ _ gens sks) = 
   "gens = " ++ (show gens) ++ 
   "\nsks = " ++ (show sks) 

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq gen, Eq sk, Eq x, Eq y, Eq gen', Eq sk', Eq x', Eq y')
  => Eq (Transform var ty sym en fk att gen sk x y gen' sk' x' y') where
 (Transform s1 s2 gens sks) == (Transform s1' s2' gens' sks')
  = (s1 == s1') && (s2 == s2') && (gens == gens') && (sks == sks') 


  
----

-- Syntax ------------------------------------------

-- todo: raw string based syntax with type inference, etc

data TypesideExp :: * -> * -> * -> * where
  TypesideLiteral :: Typeside var ty sym -> TypesideExp var ty sym
  TypesideInitial :: TypesideExp Void Void Void
   
evalTypeside :: TypesideExp var ty sym -> Either String (Typeside var ty sym)
evalTypeside (TypesideLiteral typeside) = return typeside
evalTypeside  TypesideInitial = return $ Typeside Set.empty Map.empty Set.empty undefined -- todo: replace undefined with non effectful code 

data SchemaExp :: * -> * -> * -> * -> * -> * -> * where 
  SchemaLiteral :: Schema var ty sym en fk att -> SchemaExp var ty sym en fk att
  SchemaInitial :: Typeside var ty sym -> SchemaExp var ty sym en fk att
  SchemaCoProd :: (SchemaExp var ty sym en fk att) -> 
                  (SchemaExp var ty sym en' fk' att') -> 
                   SchemaExp var ty sym 
                    (Either en en') (Either fk fk') (Either att att')

evalSchema :: SchemaExp var ty sym en fk att 
  -> Either String (Schema var ty sym en fk att)     
evalSchema (SchemaLiteral schema) = return schema 
evalSchema (SchemaInitial typeside) = return schema 
 where schema = Schema typeside Set.empty Map.empty Map.empty Set.empty Set.empty             undefined
evalSchema (SchemaCoProd s1 s2) = Left "todo"
--todo: additional schema functions


data InstanceExp :: * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * where
  InstanceLiteral :: Instance var ty sym en fk att gen sk x y ->
    InstanceExp var ty sym en fk att gen sk x y
  InstanceInitial :: Schema var ty sym en fk att ->
    InstanceExp var ty sym en fk att Void Void Void Void
 
  InstanceDelta :: 
   (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y,
    Eq en', Eq fk', Eq att') =>
   MappingExp var ty sym en fk att en' fk' att'  
   ->  InstanceExp var ty sym en' fk' att' gen sk x y
   ->  InstanceExp var ty sym en fk att (en',gen) sk (en',x) y
 
  InstanceSigma :: MappingExp var ty sym en fk att en' fk' att'  
   ->  InstanceExp var ty sym en fk att gen sk x y
   ->  InstanceExp var ty sym en fk att gen' sk' x' y'
  InstancePi :: MappingExp var ty sym en fk att en' fk' att'  
   ->  InstanceExp var ty sym en fk att gen sk x y
   ->  InstanceExp var ty sym en fk att gen' sk' x' y'
  InstanceEval :: QueryExp var ty sym en fk att en' fk' att'  
   ->  InstanceExp var ty sym en fk att gen sk x y
   ->  InstanceExp var ty sym en fk att gen' sk' x' y'
  InstanceCoEval :: MappingExp var ty sym en fk att en' fk' att'  
   ->  InstanceExp var ty sym en fk att gen' sk' x' y'
   ->  InstanceExp var ty sym en fk att gen sk x y
  


evalDeltaAlgebra ::
 (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y,
    Eq en', Eq fk', Eq att') =>
   Mapping var ty sym en fk att en' fk' att'  
   ->  Instance var ty sym en' fk' att' gen sk x y
   ->  Algebra var ty sym en fk att (en',gen) sk (en',x) y
evalDeltaAlgebra = undefined --todo

evalDeltaInst ::
 (Ord var, Ord ty, Ord sym, Ord en, Ord fk, Ord att, Ord gen, Ord sk, Eq x, Eq y,
    Eq en', Eq fk', Eq att') =>
   Mapping var ty sym en fk att en' fk' att'  
   ->  Instance var ty sym en' fk' att' gen sk x y
   ->  Instance var ty sym en fk att (en',gen) sk (en',x) y
evalDeltaInst = undefined --todo
    
evalInstance :: 
 InstanceExp var ty sym en fk att gen sk x y -> 
  Either String (Instance var ty sym en fk att gen sk x y)
evalInstance (InstanceDelta f' i') = 
 do f <- evalMapping  f' 
    i <- evalInstance i'
    if ((dst f) == (schema i)) 
      then return $ evalDeltaInst f i
      else Left $ "schemas do not match" --todo: mapping has dst " ++ (show $ dst f) ++ " but insts schema is " ++ (show $ schema i)
      

 

evalInstance (InstanceLiteral inst) = return inst  
evalInstance (InstanceInitial schema) = return $ Instance schema 
 Map.empty Map.empty Set.empty undefined $ Algebra schema 
 (Map.empty) undefined undefined
 undefined undefined undefined undefined 
 --todo: undefineds can be replaced with actually non effectful code
evalInstance _ = Left "todo"

data MappingExp :: * -> * -> * -> * -> * -> * -> * -> * -> * -> * where
 MappingId :: SchemaExp var ty sym en fk att ->
   MappingExp var ty sym en fk att en fk att
 MappingLiteral :: Mapping var ty sym en fk att en' fk' att' -> 
   MappingExp var ty sym en fk att en' fk' att'  
 
evalMapping :: MappingExp var ty sym en fk att en' fk' att' ->
  Either String (Mapping var ty sym en fk att en' fk' att')
evalMapping (MappingId schema) = Left "todo" --todo
evalMapping (MappingLiteral l) = return l 

data QueryExp :: * -> * -> * -> * -> * -> * -> * -> * -> * -> * where
 QueryId :: SchemaExp var ty sym en fk att ->
   QueryExp var ty sym en fk att en fk att
 QueryLiteral :: Query var ty sym en fk att en' fk' att' -> 
   QueryExp var ty sym en fk att en' fk' att'  
   
evalQuery :: QueryExp var ty sym en fk att en' fk' att' 
  -> Either String (Query var ty sym en fk att en' fk' att') 
evalQuery (QueryId schema) = Left "todo" --todo
evalQuery (QueryLiteral q) = return q

data TransformExp :: * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * -> * where 
 TransformId :: InstanceExp var ty sym en fk att gen sk x y ->
   TransformExp var ty sym en fk att gen sk x y gen sk x y 
 TransformLiteral :: Transform var ty sym en fk att gen sk x y gen' sk' x' y' 
   -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y' 
 
 --these types could be a little off
 TransformSigmaDeltaUnit :: MappingExp var ty sym en fk att en' fk' att'  
  -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y'    
 TransformSigmaDeltaCoUnit :: MappingExp var ty sym en fk att en' fk' att'  
  -> TransformExp var ty sym en fk' att' gen' sk x y gen' sk' x' y'    
 TransformDeltaPiUnit :: MappingExp var ty sym en fk att en' fk' att'  
  -> TransformExp var ty sym en fk' att' gen' sk x y gen' sk' x' y'    
 TransformDeltaPiCoUnit :: MappingExp var ty sym en fk att en' fk' att'  
  -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y'    
 TransformQueryUnit :: QueryExp var ty sym en fk att en' fk' att'  
  -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y'    
 TransformQueryCoUnit :: MappingExp var ty sym en fk att en' fk' att'  
  -> TransformExp var ty sym en fk' att' gen' sk x y gen' sk' x' y'    
 
 TransformDelta :: MappingExp var ty sym en fk att en' fk' att'  
   -> TransformExp var ty sym en' fk' att' gen sk x y gen' sk' x' y' 
   -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y'    
 TransformSigma :: MappingExp var ty sym en fk att en' fk' att'  
   -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y' 
   -> TransformExp var ty sym en' fk' att' gen sk x y gen' sk' x' y'    
 TransformPi :: MappingExp var ty sym en fk att en' fk' att'  
   -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y' 
   -> TransformExp var ty sym en' fk' att' gen sk x y gen' sk' x' y'    
 TransformCoEval :: QueryExp var ty sym en fk att en' fk' att'  
   -> TransformExp var ty sym en' fk' att' gen sk x y gen' sk' x' y' 
   -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y'    
 TransformEval :: QueryExp var ty sym en fk att en' fk' att'  
   -> TransformExp var ty sym en fk att gen sk x y gen' sk' x' y' 
   -> TransformExp var ty sym en' fk' att' gen sk x y gen' sk' x' y'    
    

evalTransform :: TransformExp var ty sym en fk att gen sk x y gen' sk' x' y'
 -> Either String (Transform var ty sym en fk att gen sk x y gen' sk' x' y')
evalTransform (TransformId inst  ) = Left "todo" --todo
evalTransform (TransformLiteral h) = return h 

--------------------------










main = do putStrLn $ show typesideDom
          putStrLn $ show schemaOne
          putStrLn $ show schemaTwo
          putStrLn $ show mappingTwoToOne
          putStrLn $ show instanceOne













