------------------------------- MODULE DijkstraTokenRing -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M
ASSUME N \in Nat /\ M \in Nat /\ N > 0 /\ M > 0 /\ N <= M + 1

VARIABLES c

Init == /\ c \in [0..N-1 -> 0..M-1]

CreateToken ==
    \/ /\ c[0] = c[N-1]
       /\ c' = [c EXCEPT ![0] = (c[0] + 1) % M]

PassToken(i) ==
    /\ i \in 1..N-1
    /\ c[i] # c[i-1]
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next ==
    CreateToken \/ (\E i \in 1..N-1 : PassToken(i))

Spec ==
    /\ Init
    /\ [][Next]_<<c>>
    /\ WF_next(<<c>>)

TypeOK ==
    \A i \in 0..N-1 : c[i] \in 0..M-1

Stab ==
    \E i \in 0..N-1 :
        (\A j \in 0..i-1 : c[j] = c[0])
        /\ (\A j \in i..N-1 : c[j] = (c[0] - 1) % M)

=============================================================================