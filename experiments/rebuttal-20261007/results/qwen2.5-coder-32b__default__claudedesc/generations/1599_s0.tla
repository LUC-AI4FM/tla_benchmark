------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b

Init == 
    /\ x = 0
    /\ y = 0
    /\ b = [i \in 1..N -> FALSE]

Next ==
    LET self = CHOOSE p \in 1..N: TRUE
        j = 0
    IN
    \/ /\ b[self] = FALSE
       /\ x' = self
       /\ y' = 0
       /\ b' = [b EXCEPT ![self] = TRUE]
       /\ UNCHANGED <<x, y>>
    \/ /\ b[self]
       /\ x = self
       /\ y = 0
       /\ \A i \in 1..N \ {self}: b[i] = FALSE
       /\ y' = self
       /\ UNCHANGED <<b, x>>
    \/ /\ b[self]
       /\ x = self
       /\ y # 0
       /\ b' = [b EXCEPT ![self] = FALSE]
       /\ UNCHANGED <<x, y>>
    \/ /\ b[self]
       /\ j < N
       /\ \A i \in 1..j: b[i] = FALSE
       /\ j' = j + 1
       /\ UNCHANGED <<b, x, y>>
    \/ /\ b[self]
       /\ j = N
       /\ \A i \in 1..N \ {self}: b[i] = FALSE
       /\ y # 0
       /\ y' = 0
       /\ b' = [b EXCEPT ![self] = FALSE]
       /\ UNCHANGED x
    \/ /\ b[self]
       /\ j = N
       /\ \A i \in 1..N \ {self}: b[i] = FALSE
       /\ y = self
       /\ y' = 0
       /\ b' = [b EXCEPT ![self] = FALSE]
       /\ UNCHANGED x

Spec == Init /\ [][Next]_<<x, y, b>>

Invariant ==
    \A i, j \in 1..N: i # j => \/ ~b[i] \/ ~b[j]

CondLiveness ==
    [](\/ \E p \in 1..N: ~[]<>(~b[p]))
         -> <>(\E q \in 1..N: y = q)

FairSpec == Spec /\ WF_<<x, y, b>>[Next]
=============================================================================