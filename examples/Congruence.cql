prover
    options = congruence

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
        a.manager=a a.worksIn.secretary=a
        b.manager=a b.worksIn = a.worksIn
        first(a) = Al
        first(b) = Bob  last(b) = Bo
}
