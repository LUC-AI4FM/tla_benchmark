------------------------------- MODULE OneVariableSystem -------------------------------
EXTENDS Naturals, TLC

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES x

Init == x = 0

Next == \/ /\ x = 0
              /\ x' \in {1, 2}
          \/ /\ x /= 0
              /\ x' = 0

Spec == Init /\ [][Next]_<<x>> /\ WF_x(Next)

\* Safety invariants
Invariant1 == \/ x = 0
               \/ x \in {1, 2}

\* Liveness properties
StabilizeAwayFrom1Or2 == <>[] (x \notin {1, 2})
RepeatedReturnToZero == <>(/\ x = 0 /\ [](x' # 0) => <>[] (x = 0))

\* Negation of a temporal property
NegatedProperty == ~<>(x = 1)

\* Postcondition for TLC-generated counterexample trace
Postcondition(trace) == \E i \in {1..LEN(trace)}: trace[i] = [x |-> 1]

=============================================================================