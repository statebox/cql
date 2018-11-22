{ mkDerivation, stdenv, hpack, hspec
, base, containers, megaparsec, servant-server, term-rewriting, tabular, wai
, wai-extra, warp, twee-lib, containers, union-find, fgl, mtl, PropLogic }:

mkDerivation {
  pname = "aql";
  version = "0.1.0.0";
  src = ./.;

  isLibrary = true;
  isExecutable = true;
  doCheck = true;

  libraryHaskellDepends = [
    base containers megaparsec servant-server term-rewriting tabular wai wai-extra
    warp twee-lib containers union-find fgl mtl PropLogic 
  ];
  executableHaskellDepends = [
    base containers megaparsec term-rewriting twee-lib containers union-find fgl mtl PropLogic
  ];
  testHaskellDepends = [
    base containers megaparsec term-rewriting hspec twee-lib containers union-find fgl mtl PropLogic
  ];
  buildDepends = [ hpack ];

  preConfigure = ''
    hpack
  '';

  homepage = "https://github.com/statebox/aql";
  description = "AQL - Algebraic Query Language implementation in Haskell";
  license = stdenv.lib.licenses.bsd3;
}
