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
module Language.CQL.Parser.ReservedWords where

reservedWords :: [String]
reservedWords =
  [ "sigma_chase"
  , "entity"
  , "md"
  , "quotient_jdbc"
  , "random"
  , "sql"
  , "chase"
  , "check"
  , "import_csv"
  , "quotient_csv"
  , "coproduct"
  , "simple"
  , "assert_consistent"
  , "coproduct_sigma"
  , "coequalize"
  , "html"
  , "quotient"
  , "entity_equations"
  , "schema_colimit"
  , "exists"
  , "constraints"
  , "getMapping"
  , "getSchema"
  , "typeside"
  , "schema"
  , "mapping"
  , "instance"
  , "transform"
  , "query"
  , "command"
  , "graph"
  , "exec_jdbc"
  , "exec_js"
  , "exec_cmdline"
  , "literal"
  , "add_to_classpath"
  , "identity"
  , "match"
  , "attributes"
  , "empty"
  , "imports"
  , "types"
  , "constants"
  , "functions"
  , "equations"
  , "forall"
  , "java_types"
  , "multi_equations"
  , "pi"
  , "bindings"
  , "toQuery"
  , "toCoQuery"
  , "anonymize"
  , "frozen"
  , "params"
  , "java_constants"
  , "java_functions"
  , "options"
  , "entities"
  , "src"
  , "unique"
  , "dst"
  , "path_equations"
  , "observation_equations"
  , "generators"
  , "rename"
  , "remove"
  , "modify"
  , "foreign_keys"
  , "lambda"
  , "sigma"
  , "delta"
  , "pi"
  , "unit"
  , "counit"
  , "eval"
  , "coeval"
  , "ed"
  , "chase"
  , "from"
  , "where"
  , "return"
  , "pivot"
  , "copivot"
  , "colimit"
  , "nodes"
  , "edges"
  , "typesideOf"
  , "schemaOf"
  , "distinct"
  , "import_csv"
  , "export_csv_instance"
  , "export_csv_transform"
  , "import_jdbc"
  , "import_jdbc_all"
  , "export_jdbc_transform"
  , "export_jdbc_instance"
  , "export_jdbc_query"
  , "unit_query"
  , "counit_query"
  , "union"
  , "wrap"
  ]
