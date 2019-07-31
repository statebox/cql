/*
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
*/

{ mkDerivation, stdenv, hpack, hspec
, base, containers, megaparsec, servant-server, term-rewriting, tabular, wai
, wai-extra, warp, twee-lib, union-find, fgl, mtl, PropLogic }:

mkDerivation {
  pname = "cql";
  version = "0.1.0.0";
  src = ./.;

  isLibrary = true;
  isExecutable = true;
  doCheck = true;

  libraryHaskellDepends = [
    base containers megaparsec servant-server term-rewriting tabular wai wai-extra
    warp twee-lib union-find fgl mtl PropLogic
  ];
  executableHaskellDepends = [
    base megaparsec term-rewriting twee-lib containers union-find fgl mtl PropLogic
  ];
  testHaskellDepends = [
    base megaparsec term-rewriting hspec twee-lib containers union-find fgl mtl PropLogic
  ];
  buildDepends = [ hpack ];

  preConfigure = ''
    hpack
  '';

  homepage = "https://github.com/statebox/cql";
  description = "CQL - Categorical Query Language implementation in Haskell";
  license = stdenv.lib.licenses.agpl3;
}
