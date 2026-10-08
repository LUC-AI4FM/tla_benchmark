------------------------------ MODULE I ------------------------------

EXTENDS Integers

VARIABLES x

S == 1..5

Init == x \in S

RECURSIVE G(_)
G(i) == IF i = 1 THEN 1 ELSE G(i - 1) + 1

F == [i \in S |-> G(i)]

N(i) == UNCHANGED <<x>>

Next == \E i \in 1..3: N(i)

Inv == \E i \in DOMAIN F: F[i] = x

Spec == Init /\ [][Next]_<<x>>

============================================================================