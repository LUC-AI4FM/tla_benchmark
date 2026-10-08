------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b

Init == 
    /\ x = -1
    /\ y = -1
    /\ b = [p \in 0..N-1 |-> FALSE]

Next == \/ /\ \/ /\ \/ /\ \/ /\ 
    EXIST p \in 0..N-1 : 
        /\ b[p] = FALSE
        /\ x = -1
        /\ y = -1
        /\ b' = [b EXCEPT ![p] = TRUE]
        /\ x' = p
        /\ y' = p
        /\ UNCHANGED <<other_vars>>
    \/ EXIST q \in 0..N-1 : 
        /\ p \in 0..N-1
        /\ b[p] = FALSE
        /\ q # p
        /\ (q = x)
        /\ b' = [b EXCEPT ![p] = TRUE]
        /\ y' = p
        /\ UNCHANGED <<other_vars>>
    \/ EXIST q \in 0..N-1 : 
        /\ p \in 0..N-1
        /\ b[p] = FALSE
        /\ q # p
        /\ (q # x)
        /\ (b[q])
        /\ b' = [b EXCEPT ![p] = TRUE]
        /\ y' = p
        /\ UNCHANGED <<other_vars>>
    \/ EXIST q \in 0..N-1 : 
        /\ p \in 0..N-1
        /\ b[p] = TRUE
        /\ (q = x)
        /\ (y = p)
        /\ b' = [b EXCEPT ![p] = FALSE]
        /\ x' = -1
        /\ UNCHANGED <<other_vars>>
    \/ EXIST q \in 0..N-1 : 
        /\ p \in 0..N-1
        /\ b[p] = TRUE
        /\ (q # x)
        /\ (y = p)
        /\ b' = [b EXCEPT ![p] = FALSE]
        /\ y' = -1
        /\ UNCHANGED <<other_vars>>
    \/ EXIST q \in 0..N-1 : 
        /\ p \in 0..N-1
        /\ b[p] = TRUE
        /\ (q # x)
        /\ (y # p)
        /\ y' = -1
        /\ UNCHANGED <<other_vars>>

Spec == 
    Init /\ [][Next]_<<x, y, b>> 

MutualExclusion == 
    \/ \A p,q \in 0..N-1 : 
        \/ p = q
        \/ ~(b[p] /\ (y = p))

Liveness ==
    \A p \in 0..N-1 :
        <>[](b[p] => <>(\E q \in 0..N-1 : y = q))

ConditionalLiveness ==
    \A p \in 0..N-1 :
        b[p] /\ (y = -1) => <>(\E q \in 0..N-1 : y = q)

FairnessEnhancedSpec == 
    Spec /\ WF_<<x, y, b>>[Next]

================================================================================