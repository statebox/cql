[![Build Status](https://travis-ci.com/statebox/aql.svg?branch=master&token=Ljpteop2x6Z8X4NsFyyn)](https://travis-ci.com/statebox/aql)

# AQL

Algebraic Query Language implementation in Haskell

## Building

The package can be built/tested/installed the following ways.

### Stack

Build:

`stack build`

Test:

`stack test`

Install:

`stack install`

### Cabal

Generate `.cabal` file:

`hpack`

Build:

`cabal build`

Test:

`cabal test`

Install:

`cabal install`

### Nix

Build & test:

`nix-build`

Install in current profile:

`nix-env -f . -i`

See also [default.nix](default.nix)

## API

To launch the APIs, use `stack exec alq-http`. Then you can start addressing http requests to the port 8080, with an AQL specification in the body. The `Content-Type` of the request needs to be set to `text/plain;charset=utf-8`
