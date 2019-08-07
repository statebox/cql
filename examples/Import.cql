typeside Ty = literal {
    types
        string
        nat
        int
    constants
        Al Akin Bob Bo Carl Cork Dan Dunn Math CS : string
        zero : nat
        one  : int
    functions
        succ : nat -> nat
        plus : nat, nat -> nat
    equations
        forall x:nat. plus(zero, x) = x
        forall x y:nat. plus(succ(x),y) = succ(plus(x,y))
    options
        program_allow_nontermination_unsafe=true
}

typeside Ty2 = literal {
    types
        string2
        nat
    constants
        sdds sdfiodf wefew fffd : string2
        zero : nat
    functions
        succ : nat -> nat
        plus : nat, nat -> nat
    equations
        forall x   : nat. plus(zero,   x) = x
        forall x y : nat. plus(succ(x),y) = succ(plus(x,y))
    options
        program_allow_nontermination_unsafe=true
}

typeside Ty3 = literal {
    imports Ty Ty2
    options
        program_allow_nontermination_unsafe=true
}

schema C = literal : Ty {
    entities
        T1 T2
    foreign_keys
        f : T1 -> T2
        g : T2 -> T2
    path_equations
        g.g = g
    attributes
        ssn first1 last1 : T1 -> string
        first2 last2     : T2 -> string
        salary           : T2 -> int
    observation_equations
        //forall x. x.ssn = x.first1
    options
        program_allow_nontermination_unsafe=true
        allow_empty_sorts_unsafe = true
}

schema D = literal : Ty {
    entities
        T
    attributes
        ssn0 first0 last0 : T -> string
        salary0           : T -> int
    options
        program_allow_nontermination_unsafe=true
        allow_empty_sorts_unsafe = true
}

schema E = literal : Ty {
    imports C D
    options
        program_allow_nontermination_unsafe=true
        allow_empty_sorts_unsafe = true
}

instance I = literal : D {
    generators
        i   : int
        s t : T
    equations
        t.ssn0 = t.last0
    options
        program_allow_nontermination_unsafe=true
        allow_empty_sorts_unsafe = true
}


instance J = literal : D {
    generators
        t0 : T
    equations
        t0.ssn0 = t0.last0
    options
        program_allow_nontermination_unsafe=true
        allow_empty_sorts_unsafe = true
}

instance K = literal : D {
    imports I J
    options
        program_allow_nontermination_unsafe=true
        allow_empty_sorts_unsafe = true
}

transform h1 = identity I
transform h2 = identity J
transform h = literal : K -> K {
    imports h1 h2
}

mapping F = literal : C -> D {
    entity
        T1 -> T
    foreign_keys
        f -> T
    attributes
        ssn    -> lambda x. ssn0(x)
        first1 -> lambda x. first0(x)
        last1  -> lambda x. x.last0

    entity
        T2 -> T
    foreign_keys
        g -> T
    attributes
        last2  -> lambda x. x.last0
        salary -> lambda x. x.salary0
        first2 -> lambda x. x.first0
}

mapping F2 = identity D

mapping G = literal : E -> E {
    imports F F2
}
