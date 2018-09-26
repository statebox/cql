{ mkDerivation, stdenv, hpack, base, containers, hspec, megaparsec }:
mkDerivation {
  pname = "aql";
  version = "0.1.0.0";
  src = ./.;

  isLibrary = true;
  isExecutable = true;
  doCheck = true;

  buildDepends = [ hpack ];
  libraryHaskellDepends = [ base containers megaparsec ];
  executableHaskellDepends = [ base containers megaparsec ];
  testHaskellDepends = [ base containers hspec megaparsec ];

  preConfigure = ''
    hpack
  '';

  homepage = "https://github.com/statebox/aql";
  description = "AQL - Algebraic Query Language implementation in Haskell";
  license = stdenv.lib.licenses.bsd3;
}
