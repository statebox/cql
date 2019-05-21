[![Build Status](https://travis-ci.com/statebox/aql.svg?branch=master&token=Ljpteop2x6Z8X4NsFyyn)](https://travis-ci.com/statebox/aql) [![License: AGPL v3](https://img.shields.io/badge/License-AGPL%20v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)

> Note: AQL has been renamed to CQL.
> We still need to fix this in the code [#140](https://github.com/statebox/cql/issues/140)

# CQL

Categorical Query Language implementation in Haskell.

## Example

After building, you can use `aql-exe` to evaluate a `.aql` file, e.g.

```sh
# build it
stack build

# run `aql-exe` on `examples/Employee.aql`
.stack-work/dist/x86_64-osx/Cabal-2.2.0.1/build/aql-exe/aql-exe examples/Employee.aql
```

Here is an example of what an `.aql` file looks like

```
options
  program_allow_nontermination_unsafe = true
  allow_empty_sorts_unsafe = true

typeside T = literal {
  types
    string
    nat

  constants
    Al Akin Bob Bo Carl Cork Dan Dunn Math CS : string
    zero : nat

  functions
    succ : nat -> nat
    plus : nat, nat -> nat
}

schema S = literal : T {
  entities
    Employee
    Department

  foreign_keys
    manager   : Employee -> Employee
    worksIn   : Employee -> Department
    secretary : Department -> Employee

  attributes
    first last : Employee -> string
    age : Employee -> nat
    name : Department -> string
}

instance I = literal : S {
  generators
    a b : Employee

  equations
    a.manager = a
    a.worksIn.secretary = a
    b.manager = a
    b.worksIn = a.worksIn
    last(b) = Bo

  multi_equations
    first -> {a Al, b Bob}
}

instance J = literal : S {
  generators
    a b : Employee
    c d : Department
    y : nat

  equations
    a.manager = a
    a.worksIn = d
    c.secretary = b
    b.manager = a
    b.worksIn = c
    d.secretary = b
    first(a) = Al
    a.last = Al
    d.name = Bob
    c.name = Al
    age(a) = zero
    age(b) = y

  options interpret_as_algebra = true
}
```

## Documentation

Paper describing how CQL (then still called AQL) is implemented: https://arxiv.org/abs/1503.03571
AQL user manual: https://categoricaldata.net/aqlmanual.pdf
Java version: https://github.com/CategoricalData/fql

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

### License

Unless explicitly stated otherwise all files in this repository are licensed under the GNU Affero General Public License.

Copyright © 2019 [Stichting Statebox](https://statebox.nl).
