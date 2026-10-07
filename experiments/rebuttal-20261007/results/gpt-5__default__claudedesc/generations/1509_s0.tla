------------------------------ MODULE I ------------------------------

EXTENDS Naturals, Integers

VARIABLES x

S == 1..5
Indices == 1..3

RECURSIVE G(_)
G(i) == IF i = 1 THEN 1 ELSE G(i - 1) + 1

F == [i \in S |-> G(i)]

Init == x \in S

N(i) == UNCHANGED <<x>>
Next == \E i \in Indices: N(i)

vars == << x >>

Inv == \E i \in DOMAIN F: F[i] = x
Safety == []Inv

Spec == Init /\ [][Next]_vars

=============================================================================