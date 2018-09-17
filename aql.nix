{ mkDerivation, base, containers, hspec, megaparsec, stdenv }:
mkDerivation {
  pname = "aql";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  doCheck = true;
  libraryHaskellDepends = [ base containers megaparsec ];
  executableHaskellDepends = [ base containers megaparsec ];
  testHaskellDepends = [ base containers hspec megaparsec ];
  homepage = "https://github.com/statebox/aql#readme";
  license = stdenv.lib.licenses.bsd3;
}
