---- MODULE EWD426 ----

CONSTANTS N, M

VARIABLES c

ASSUME N \in Nat /\ N > 0
ASSUME M \in Nat /\ M > 0
ASSUME N <= M + 1

CreateToken == 
    /\ c[0] = c[N-1]
    /\ c' = [c EXCEPT ![0] = (c[0] + 1) % M]

PassToken(i) ==
    /\ i \in 1..N-1
    /\ c[i] # c[i-1]
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next == 
    \/ CreateToken
    \/ \E i \in 1..N-1 : PassToken(i)

Spec == 
    /\ Init
    /\ [][Next]_<<c>>
    /\ WF_next(Next)

Init == 
    /\ c \in [0..N-1 -> 0..M-1]

TypeOK ==
    /\ c \in [0..N-1 -> 0..M-1]

TokenExists ==
    \E i \in 0..N-1 : 
        (\A j \in 0..i-1 : c[j] = c[0])
        /\ (\A j \in i..N-1 : c[j] = (c[0] - 1) % M)

Stab ==
    <>[] TokenExists

THEOREM Spec => []TypeOK /\ <><>Stab

====