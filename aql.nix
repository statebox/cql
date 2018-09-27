{ mkDerivation, stdenv, hpack, base, containers, hspec, megaparsec, multiset, union-find-array, term-rewriting }:
mkDerivation {
  pname = "aql";
  version = "0.1.0.0";
  src = ./.;

  isLibrary = true;
  isExecutable = true;
  doCheck = true;

  buildDepends = [ hpack ];
  libraryHaskellDepends = [ base containers megaparsec multiset union-find-array term-rewriting ];
  executableHaskellDepends = [ base containers megaparsec multiset union-find-array term-rewriting ];
  testHaskellDepends = [ base containers hspec megaparsec multiset union-find-array term-rewriting ];

  preConfigure = ''
    hpack
  '';

  homepage = "https://github.com/statebox/aql";
  description = "AQL - Algebraic Query Language implementation in Haskell";
  license = stdenv.lib.licenses.bsd3;
}
