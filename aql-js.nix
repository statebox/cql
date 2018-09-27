{ mkDerivation, stdenv, hpack, ghcjs-base, base, containers, hspec, megaparsec }:
mkDerivation {
  pname = "aql-js";
  version = "0.1.0.0";
  src = ./.;

  isLibrary = true;
  isExecutable = true;
  doCheck = true;

  buildDepends = [ hpack ];
  libraryHaskellDepends = [ ghcjs-base base containers megaparsec ];
  executableHaskellDepends = [ ghcjs-base base containers megaparsec ];
  testHaskellDepends = [ ghcjs-base base containers hspec megaparsec ];

  preConfigure = ''
    hpack
  '';

  homepage = "https://github.com/statebox/aql";
  description = "AQL - Algebraic Query Language implementation in Haskell";
  license = stdenv.lib.licenses.bsd3;
}
