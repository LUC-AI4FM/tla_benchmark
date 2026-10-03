---- MODULE RecursiveFunctionSpec ----
EXTENDS Integers, TLC

VARIABLES x

\* A recursively-defined operator over a finite domain.
F[n \in {1,2,3,4,5}] ==
    IF n = 1 THEN 1
    ELSE n + F[n-1]

\* An indexed state/action operator.
N(i) == x' = x + i

\* The initial state predicate.
Init == x = 1

\* The next-state relation, defined as an existential over the indexed action.
Next == \E i \in {1, 2, 3} : N(i)

\* The complete temporal specification, allowing stuttering steps.
Spec == Init /\ [][Next]_x

\* A safety invariant relating the state variable x to a value of F.
Inv == x >= F[1]

====================================