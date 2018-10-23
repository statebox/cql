{ mkDerivation, stdenv, hpack, hspec
, base, containers, megaparsec, servant-server, term-rewriting, tabular, wai
, wai-extra, warp }:

mkDerivation {
  pname = "aql";
  version = "0.1.0.0";
  src = ./.;

  isLibrary = true;
  isExecutable = true;
  doCheck = true;

  libraryHaskellDepends = [
    base containers megaparsec servant-server term-rewriting tabular wai wai-extra
    warp
  ];
  executableHaskellDepends = [
    base containers megaparsec term-rewriting
  ];
  testHaskellDepends = [
    base containers megaparsec term-rewriting hspec
  ];
  buildDepends = [ hpack ];

  preConfigure = ''
    hpack
  '';

  homepage = "https://github.com/statebox/aql";
  description = "AQL - Algebraic Query Language implementation in Haskell";
  license = stdenv.lib.licenses.bsd3;
}
