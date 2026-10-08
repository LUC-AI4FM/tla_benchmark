------------------------------- MODULE TokenRing -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M
ASSUME N \in Nat /\ N >= 1
ASSUME M \in Nat /\ M >= 1
ASSUME N <= M + 1

VARIABLES values

Init == /\ values \in [0..N-1 -> 0..M-1]
      /\ \/ \A i \in 0..N-2 : values[i] = values[i+1]
         \/ values[N-1] # values[0]

Next ==
    \/ /\ \/ \E i \in 1..N-1 : values[i] # values[(i-1) % N]
          /\ values' = [values EXCEPT ![i] = values[(i-1) % N]]
       [] /\ values[N-1] # values[0]
          /\ values' = [values EXCEPT ![0] = (values[N-1] + 1) % M]
    \/ /\ \A i \in 0..N-1 : values[i] = values[(i-1) % N]
       /\ values' = values

Spec == Init /\ [][Next]_<<values>>

Stabilization ==
    \E tokenValue \in 0..M-1 :
        \A i \in 0..N-2 : values[i] = tokenValue
        /\ values[N-1] = tokenValue

Invariant == Spec => []Stabilization

Fairness == WF_next(<<values>>)

THEOREM Spec => Invariant
=============================================================================