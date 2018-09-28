{ mkDerivation, stdenv, hpack, hspec
, ghcjs-base, base, containers, megaparsec, term-rewriting }:

mkDerivation {
  pname = "aql";
  version = "0.1.0.0";
  src = ./.;

  isLibrary = true;
  isExecutable = true;
  doCheck = true;

  libraryHaskellDepends = [
    ghcjs-base base containers megaparsec term-rewriting
  ];
  executableHaskellDepends = [
    ghcjs-base base containers megaparsec term-rewriting
  ];
  testHaskellDepends = [
    ghcjs-base base containers megaparsec term-rewriting hspec
  ];
  buildDepends = [ hpack ];

  preConfigure = ''
    hpack
  '';

  homepage = "https://github.com/statebox/aql";
  description = "AQL - Algebraic Query Language implementation in Haskell";
  license = stdenv.lib.licenses.bsd3;
}
