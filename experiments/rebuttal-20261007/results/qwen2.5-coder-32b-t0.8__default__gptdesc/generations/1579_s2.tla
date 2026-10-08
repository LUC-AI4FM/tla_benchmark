------------------------------- MODULE DijkstraTokenRing ------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N, K

VARIABLES values

Init == /\ Len(values) = N
        /\ \A i \in 0..N-1 : values[i] \in 0..K-1

Next ==
    \/ \E i \in 0..N-1 :
         LET predecessor = (i - 1) % N
             currentValue = values[i]
             predecessorValue = values[predecessor]
         IN /\ i # 0 -> currentValue' = IF currentValue # predecessorValue THEN predecessorValue ELSE currentValue
            /\ i = 0 -> currentValue' = IF currentValue = predecessorValue THEN (currentValue + 1) % K ELSE currentValue
        /\ \A j \in 0..N-1 : j # i -> values'[j] = values[j]

Spec ==
    /\ Init
    /\ [][Next]_<<values>>
    /\ WF_next(<<values>>)

IsTokenHolder(i) == (i = 0 /\ values[0] = values[N-1]) \/ (\A predecessor \in 0..N-2 : values[(predecessor + 1) % N] # values[predecessor])

Safety ==
    /\ \A i, j \in 0..N-1 : i # j -> ~(IsTokenHolder(i) /\ IsTokenHolder(j))
    /\ \E i \in 0..N-1 : IsTokenHolder(i)

Liveness ==
    \/ Stable
    \/ EventualSingleToken

Stable == \A i \in 0..N-1 : values[i] = values[(i + 1) % N]

EventualSingleToken ==
    <>[] (\E i \in 0..N-1 : IsTokenHolder(i)) /\ []<>(\A i, j \in 0..N-1 : i # j -> ~(IsTokenHolder(i) /\ IsTokenHolder(j)))

=============================================================================