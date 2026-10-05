---------------------------- MODULE I ----------------------------
EXTENDS Integers

CONSTANTS S, Indices

VARIABLES x

F == [i \in S |-> IF i = 1 THEN 1 ELSE F[i-1] + 1]

N(i) == UNCHANGED <<x>>

Init == x \in S

Next == \E i \in Indices : N(i)

Inv == \E i \in DOMAIN F : F[i] = x

Spec == Init /\ [][Next]_<<x>>

====