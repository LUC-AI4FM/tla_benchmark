---------------------------- MODULE RecursiveSpec ----------------------------

EXTENDS Naturals

VARIABLES x

\* Recursively specified function-like operator F over the set {1,2,3,4,5}
F[n \in {1,2,3,4,5}] ==
    IF n = 1 THEN 1
    ELSE n * F[n - 1]

\* State/action-style operator N indexed by {1,2,3}
N(i) == i \in {1,2,3} /\ x' = x + i

\* Initial state predicate
Init == x = 1

\* Next state relation: existentially quantified indexed action
Next == \E i \in {1,2,3} : N(i)

\* Temporal specification: Init and always Next under stuttering
Spec == Init /\ [][Next]_x

\* Invariant relating x to values of F
Inv == x \in {F[n] : n \in {1,2,3,4,5}} \/ x \in 1..F[5]

=============================================================================