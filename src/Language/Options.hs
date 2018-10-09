{-# LANGUAGE EmptyDataDeriving #-}

module Language.Options where
import           Data.Char
import           Data.Map.Strict as Map
import           Language.Common
import           Text.Read

data Options = Options {
  iOps :: Map IntOption Integer,
  bOps :: Map BoolOption Bool,
  sOps :: Map StringOption String
--  cOps :: Map CharOption Char
}

toOptions :: [(String, String)] -> Err Options
toOptions [] = return defaultOptions
toOptions ((k,v):l) =  do Options s t u <- toOptions l
                          case a of
                            Left _ -> case b of
                              Left _ -> do (o,i) <- c
                                           return $ Options s t (Map.insert o i u)
                              Right (o,i) -> return $ Options s (Map.insert o i t) u
                            Right (o, i)  -> return $ Options (Map.insert o i s) t u
 where a = toIntegerOption (k, v)
       b = toBoolOption (k, v)
       c = toStringOption (k, v)


toIntegerOption :: (String, String) -> Err (IntOption, Integer)
toIntegerOption (k,v) = case matches of
                        [] -> Left $ "No option called " ++ k
                        (x:_) -> do a <- parseInt v
                                    return (x, a)
  where matches = [ k' | k' <- opsI, toLowercase (show k') == k ]
        parseInt :: String -> Err Integer
        parseInt x = case readMaybe x of
                      Nothing -> Left $ "Not an int: " ++ x
                      Just y  -> Right y


toStringOption :: (String, String) -> Err (StringOption, String)
toStringOption (k,v) = case matches of
                        []    -> Left $ "No option called " ++ k
                        (x:_) -> do return (x, v)
  where matches = [ k' | k' <- opsS, toLowercase (show k') == k ]

toLowercase :: String -> String
toLowercase = Prelude.map toLower

toBoolOption :: (String, String) -> Err (BoolOption, Bool)
toBoolOption (k,v) = case matches of
                        [] -> Left  $ "No option called " ++ k
                        (x:_) -> do a <- parseBool v
                                    return (x, a)
  where matches = [ k' | k' <- opsB, toLowercase (show k') == k ]
        parseBool "true"  = Right True
        parseBool "false"=Right False
        parseBool x       = Left $ "Not a bool: " ++ x

boolDef :: [(BoolOption, Bool)]
boolDef = [(Program_Allow_Nontermination_Unsafe, False), (Allow_Empty_Sorts_Unsafe, False)]

defaultOptions :: Options
defaultOptions = Options Map.empty (Map.fromList boolDef) Map.empty

generateEnumValues :: (Enum a) => [a]
generateEnumValues = enumFrom (toEnum 0)

opsB :: [BoolOption]
opsB = generateEnumValues

opsI :: [IntOption]
opsI = generateEnumValues

opsS :: [StringOption]
opsS = generateEnumValues

--opsC :: [StringOption]
--opsC = generateEnumValues

data BoolOption =
    Require_Consistency
  | Schema_Only
--  | Allow_Java_Eqs_Unsafe
  | Dont_Validate_Unsafe
  | Always_Reload
--  | Query_Compose_Use_Incomplete
  | Query_Remove_Redundancy
  | Import_As_Theory
  | Import_Joined
  | Prepend_Entity_On_Ids
  | Program_Allow_Nontermination_Unsafe
  | Allow_Empty_Sorts_Unsafe
  | Csv_Generate_Ids
  | Completion_Sort
  | Completion_Compose
  | Completion_Filter_Subsumed
  | Completion_Syntactic_Ac
  | Eval_Reorder_Joins
  | Eval_Join_Selectivity
  | Eval_Use_Indices
  | Eval_Approx_Sql_Unsafe
  | Eval_Sql_PersistentIndices
  | Coproduct_Allow_Collisions
  deriving (Eq, Ord, Show, Enum)

data StringOption =
    Csv_File_Extension
  | Id_Column_
  | Jdbc_Default_Class
  | Jdbc_Default_String
  | Completion_Precedence
  | Prover
  deriving (Eq, Ord, Show, Enum)

prover_name :: StringOption
prover_name = Prover -- for name collision

data IntOption =
    Num_Threads
  | Random_Seed
  | Timeout
  | Varchar_Length
  | Start_Ids_At
  | Gui_Max_Graph_Size
  | Gui_Max_String_Size
  | Gui_Rows_To_Display
  | Eval_Max_Plan_Depth
  deriving (Eq, Ord, Show, Enum)

data CharOption =
    Csv_Escape_Char
  | Csv_Quote_Char
  deriving (Eq, Ord, Show, Enum)

--  | CompletionPrecedence [String]
