--------------------------- MODULE DijkstraRing ---------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, M

ASSUME 1 <= N
ASSUME 0 < M
ASSUME N <= M + 1

VARIABLES state

DOMAIN == 0 .. M-1

Init ==
    state \in [1..N -> DOMAIN]

Next ==
    \E i \in 1..N :
        LET prev   == IF i = 1 THEN N ELSE i-1
            newVal == IF state[i] != state[prev]
                      THEN state[prev]
                      ELSE (state[i] + 1) \mod M
        IN state' = [state EXCEPT ![i] = newVal]

UniqueToken ==
    (\#({i \in 1..N : state[i] = 0}) = 1)

Spec == Init /\ [][Next]_<<state>>

THEOREM Stabilization ==
    Spec => \diamond\square UniqueToken
=============================================================================