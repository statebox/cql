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

Generate docs:

`stack haddock aql`

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

## HTTP API

To launch the APIs, use `stack exec aql-http`. Then you can send http requests to port 8080, with an AQL specification in the body. The `Content-Type` of the request needs to be set to `text/plain;charset=utf-8`

For example, you could try using `cURL` as follows

```
curl -X POST \
  http://localhost:8080/aql \
  -H 'Content-Type: text/plain;charset=utf-8' \
  --data-binary "@./examples/Employee.aql"
```

You can set the following environment variables to customise the behaviour of the endpoint:

- `AQL_ENV`: Should be `Development` or `Production`. Regulates the verbosity of the console output.

- `PORT`: determines on which port the endpoint is exposed
