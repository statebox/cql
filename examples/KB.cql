//one = two should not be provable
/*
typeside EmptySortsCheck = literal {
    types
        void
        nat
    constants
        one two : nat
    equations
         forall x:void. one = two
    options
        prover = completion
        allow_empty_sorts_unsafe = true
}
*/
options
    prover = completion
    allow_empty_sorts_unsafe = true
    require_consistency = false

typeside Group = literal {
    types
        S
    constants
        e : S
    functions
        I : S -> S
        o : S,S -> S
    equations
        forall x. (e o x) = x
        forall x. (I(x) o x) = e
        forall x, y, z. ((x o y) o z) = (x o (y o z))

}

schema G = literal : Group {
    entities
        E
    attributes
        g : E -> S
}

instance AGroup = literal : G {
    generators
        e : E
    equations
        e.g.I = e.g
        (e.g o e.g) = e.g
}

/*
typeside CompletedGroup = literal {
    types
        S
    constants
        e : S
    functions
        I : S -> S
        o : S,S -> S
    equations
        forall x. (e o x) = x
        forall x. (I(x) o x) = e
        forall x, y, z. ((x o y) o z) = (x o (y o z))

        forall x, y. (I(x) o (x o y)) = y
        forall . I(e) = e
        forall x. (x o e) = x
        forall x. I(I(x)) = x
        forall x. (x o I(x)) = e
        forall x y. (x o (I(x) o y)) = y
        forall x y. I((x o y)) = (I(y) o I(x))

    options
        prover = completion
}
*/
