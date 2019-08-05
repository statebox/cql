# CQL

[![Build Status](https://travis-ci.com/statebox/cql.svg?branch=master&token=Ljpteop2x6Z8X4NsFyyn)](https://travis-ci.com/statebox/cql)
[![License: AGPL v3](https://img.shields.io/badge/License-AGPL%20v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)

Categorical Query Language (CQL) implementation in Haskell.


## About

[CQL](https://www.categoricaldata.net) is a functional query language that allows you to specify data migrations declaratively, in a way that guarantees their correctness.

It is the culmination of years of original mathematical [research](https://www.categoricaldata.net/papers) after the right balance between flexibility and correctness. Its solid grounding in category theory sets it apart from its ad hoc counterparts, and enables the compositional development and analysis of data transformations to a degree previously impossible.

CQL, formerly known as AQL, was developed by [Statebox](https://www.statebox.org) in collaboration with [Conexus](http://conexus.ai/), who develop the [Java version](https://github.com/CategoricalData/cql) of CQL.

[Learn more](https://www.categoricaldata.net).

## Example

After building, you can use `cql` to evaluate a `.cql` file, e.g.

```sh
# build it
stack build

# run `cql` on `examples/Employee.cql`
stack exec cql examples/Employee.cql
```

Here is an example of what a `.cql` file looks like:

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

`stack haddock cql`

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

To launch the APIs, use `stack exec cql-http`. Then you can send http requests to port 8080, with an CQL specification in the body. The `Content-Type` of the request needs to be set to `text/plain;charset=utf-8`

For example, you could try using `cURL` as follows

```
curl -X POST \
  http://localhost:8080/cql \
  -H 'Content-Type: text/plain;charset=utf-8' \
  --data-binary "@./examples/Employee.cql"
```

You can set the following environment variables to customise the behaviour of the endpoint:

- `CQL_ENV`: Should be `Development` or `Production`. Regulates the verbosity of the console output.

- `PORT`: determines on which port the endpoint is exposed

### License

Unless explicitly stated otherwise all files in this repository are licensed under the GNU Affero General Public License.

Copyright © 2019 [Stichting Statebox](https://statebox.nl).
