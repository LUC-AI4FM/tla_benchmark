---- MODULE Countdown ----
EXTENDS Naturals

\* For model checking, assign a concrete value in the TLC model, e.g. N <- 4
CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLE counter

vars == << counter >>

TypeOK == counter \in 0..N

Init == counter = N

Decrement ==
    /\ counter > 0
    /\ counter' = counter - 1

Done ==
    /\ counter = 0
    /\ UNCHANGED counter

Next == Decrement \/ Done

Spec == Init /\ [][Next]_vars

\* Key safety property: the counter never goes negative
NonNegative == counter >= 0

THEOREM Spec => [](TypeOK /\ NonNegative)

====