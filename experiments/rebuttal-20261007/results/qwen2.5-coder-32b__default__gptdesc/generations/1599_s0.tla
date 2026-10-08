------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b \* Shared variables

Init == 
    /\ x = 0
    /\ y = 0
    /\ b = <<FALSE>> ^ N

Next ==
    \/ \E i \in 1..N : 
        (x = 0) /\ (y = 0) /\ (b[i] = FALSE) /\ 
        (/\ x' = i
         /\ y' = 0
         /\ b' = [b EXCEPT ![i] = TRUE])
    \/ \E i \in 1..N : 
        (x = i) /\ (y = 0) /\ (b[i] = TRUE) /\ 
        (/\ x' = i
         /\ y' = i
         /\ b' = b)
    \/ \E i \in 1..N : 
        (x = i) /\ (y = i) /\ (b[i] = TRUE) /\ 
        (/\ x' = 0
         /\ y' = 0
         /\ b' = [b EXCEPT ![i] = FALSE])

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b>>
    /\ WF_x(Next)
    /\ SF_y(Next)

MutualExclusion ==
    \A i, j \in 1..N : 
        (i # j) => ~((y = i) /\ (y = j))

Liveness ==
    \A i \in 1..N :
        <>[](x = i) /\ <>[](y = i)

ConditionalLiveness ==
    \A i \in 1..N :
        <>(\E j \in 1..N : b[j]) => <>[](y = i)

FairSpec ==
    Spec /\ MutualExclusion /\ Liveness /\ ConditionalLiveness

=============================================================================