------------------------------- MODULE DijkstraTokenRing -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M
ASSUME N \in Nat /\ N >= 1
ASSUME M \in Nat /\ M >= 1
ASSUME N <= M + 1

VARIABLES values

Init == 
    /\ values \in [0..N-1 -> 0..M-1]
    /\ (\E i \in 0..N-1 : values[i] = 0)

Next ==
    \/ /\ values[0]' = (values[N-1] + 1) % M
       /\ \A j \in 1..N-1 : values[j]' = values[j]
    \/ \E i \in 1..N-1 :
        /\ values[i]' = IF values[i] # values[(i-1) % N] THEN values[(i-1) % N] ELSE values[i]
        /\ \A j \in (0..N-1) \ {i} : values[j]' = values[j]

Spec == 
    /\ Init
    /\ [][Next]_<<values>>

Stabilization ==
    \E stableValues \in [0..N-1 -> 0..M-1] :
        \/ /\ stableValues[0] = 0
           /\ \A j \in 1..N-1 : stableValues[j] # stableValues[(j-1) % N]
        \/ /\ \A i \in 0..N-1 : stableValues[i] = stableValues[(i+1) % N]
    /\ <>[](\E tokenHolder \in 0..N-1 : 
            values[tokenHolder] = 0 
            /\ (\A j \in (tokenHolder+1)..(tokenHolder+N-2) % N : values[j] # 0))

WF_Values == WF_vars(values)

THEOREM Spec => []<>(Stabilization)

=============================================================================