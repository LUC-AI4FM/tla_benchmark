---- MODULE ModularCounter ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLE x

vars == << x >>

Values == 0 .. (N - 1)

TypeOK == x \in Values

Init == x = 0

Increment == x' = (x + 1) % N

Next == Increment

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

\* Safety: counter always within valid range (0 .. N-1, i.e. 0..4 when N = 5)
RangeInv == x \in Values

\* Increment preserves the cyclic invariant
IncrementPreservesInv == [][RangeInv => RangeInv']_vars

\* Determinism: any change of x is exactly the cyclic successor
Deterministic == [][x' = (x + 1) % N]_vars

\* Liveness: under fairness, every value is eventually reached
EventuallyAll == \A v \in Values : <>(x = v)

\* Liveness: every value is visited infinitely often (indefinite cycling)
CyclesForever == \A v \in Values : []<>(x = v)

THEOREM Spec => []TypeOK
THEOREM FairSpec => CyclesForever

\* Concrete instance with maximum value 4 (5 distinct values: 0..4)
====