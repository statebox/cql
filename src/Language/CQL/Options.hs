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
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE DerivingStrategies #-}

module Language.CQL.Options where

import           Data.Void
import           Language.CQL.Common (Err, intercalate, lower)
import           Text.Read

data Options = Options {
  iOps :: IntOption -> Integer,
  bOps :: BoolOption -> Bool,
  sOps :: StringOption -> String
--  cOps :: Map CharOption Char -- not needed for now
}

instance Show Options where
  show y = intercalate "\n" (map (\x -> show x ++ " = " ++ show (iOps y x)) opsI) ++ "\n" ++
           intercalate "\n" (map (\x -> show x ++ " = " ++ show (bOps y x)) opsB) ++ "\n" ++
           intercalate "\n" (map (\x -> show x ++ " = " ++      (sOps y x)) opsS)

toOptions :: Options -> [(String, String)] -> Err Options
toOptions o [] = return o
toOptions def ((k,v):l)   = do
  Options s t u <- toOptions def l
  case a of
    Left _ -> case b  of
      Left  _      -> do { (o, i) <- c ; return $ Options s t (f o i u) }
      Right (o, i) -> return $ Options s (f o i t)   u
    Right   (o, i) -> return $ Options   (f o i s) t u
  where
    a = toIntegerOption (k, v)
    b = toBoolOption (k, v)
    c = toStringOption (k, v)
    f j u m x = if j == x then u else m x


toIntegerOption :: (String, String) -> Err (IntOption, Integer)
toIntegerOption (k, v) = case matches of
  []    -> Left $ "No option called " ++ k
  (x:_) -> do { a <- parseInt v ; return (x, a) }
  where
    matches = [ k' | k' <- opsI, lower (show k') == k ]
    parseInt :: String -> Err Integer
    parseInt x = case readMaybe x of
      Nothing -> Left  $ "Not an int: " ++ x
      Just y  -> Right y


toStringOption :: (String, String) -> Err (StringOption, String)
toStringOption (k,v) = case matches of
  []    -> Left $ "No option called " ++ k
  (x:_) -> return (x, v)
  where
    matches = [ k' | k' <- opsS, lower (show k') == k ]


toBoolOption :: (String, String) -> Err (BoolOption, Bool)
toBoolOption (k,v) = case matches of
  []    -> Left  $ "No option called " ++ k
  (x:_) -> do { a <- parseBool v ; return (x, a) }
  where
    matches = [ k' | k' <- opsB, lower (show k') == k ]
    parseBool z = case z of
      "true"  -> Right True
      "false" -> Right False
      x       -> Left $ "Not a bool: " ++ x

-- | Default values for Boolean options.
boolDef :: BoolOption -> Bool
boolDef o = case o of
  Program_Allow_Nontermination_Unsafe -> False
  Allow_Empty_Sorts_Unsafe            -> False
  Program_Allow_Nonconfluence_Unsafe  -> False
  Dont_Validate_Unsafe                -> False
  Interpret_As_Algebra                -> False
  Require_Consistency                 -> True

-- | Default values for Integer options.
intDef :: IntOption -> Integer
intDef o = case o of
  Timeout -> 30

-- | Default values for String options.
stringDef :: StringOption -> String
stringDef o = case o of
  Prover -> "auto"

-- | Default options.
defaultOptions :: Options
defaultOptions = Options intDef boolDef stringDef

-- | Returns a list of all enums in a given class.
generateEnumValues :: (Enum a) => [a]
generateEnumValues = enumFrom (toEnum 0)

-- | All the Boolean options.
opsB :: [BoolOption]
opsB = generateEnumValues

-- | All the Integer options.
opsI :: [IntOption]
opsI = generateEnumValues

-- | All the String options.
opsS :: [StringOption]
opsS = generateEnumValues

-- comment out options we can't handle yet.
data BoolOption =
      Require_Consistency
    | Dont_Validate_Unsafe
--    | Always_Reload
    | Program_Allow_Nonconfluence_Unsafe
    | Interpret_As_Algebra
    | Program_Allow_Nontermination_Unsafe
    | Allow_Empty_Sorts_Unsafe
--  | Schema_Only
--  | Query_Remove_Redundancy
--  | Import_As_Theory
--  | Import_Joined
--  | Prepend_Entity_On_Ids
--  | Csv_Generate_Ids
--  | Completion_Sort
--  | Completion_Compose
--  | Completion_Filter_Subsumed
--  | Completion_Syntactic_Ac
--  | Eval_Reorder_Joins
--  | Eval_Join_Selectivity
--  | Eval_Use_Indices
--  | Eval_Approx_Sql_Unsafe
--  | Eval_Sql_PersistentIndices
--  | Coproduct_Allow_Collisions
  deriving stock (Eq, Ord, Show, Enum)

data StringOption =
 --   Csv_File_Extension
 -- | Id_Column_
 -- | Jdbc_Default_Class
 -- | Jdbc_Default_String
 -- | Completion_Precedence
    Prover
  deriving stock (Eq, Ord, Show, Enum)

-- | Accessor due to namespace colision.
prover_name :: StringOption
prover_name = Prover -- for name collision

data IntOption =
--    Num_Threads
--  | Random_Seed
    Timeout
--  | Varchar_Length
--  | Start_Ids_At
--  | Gui_Max_Graph_Size
--  | Gui_Max_String_Size
--  | Gui_Rows_To_Display
--  | Eval_Max_Plan_Depth
  deriving stock (Eq, Ord, Show, Enum)

type CharOption = Void
 --data CharOption =
 --  Csv_Escape_Char
 --  Csv_Quote_Char
 --  deriving stock (Eq, Ord, Show, Enum)
