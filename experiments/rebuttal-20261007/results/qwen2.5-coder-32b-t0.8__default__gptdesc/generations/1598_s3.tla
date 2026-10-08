------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, S

Init == 
    /\ x = 1
    /\ y = 1
    /\ b = [p \in 1..N -> FALSE]
    /\ S = [p \in 1..N -> {}]

ProcessSetup(p) ==
    /\ x' = p
    /\ y' = p
    /\ b' = [b EXCEPT ![p] = TRUE]
    /\ S' = [S EXCEPT ![p] = (S[p] \cup {x}) \ {y}]

Retry(p) ==
    /\ y' = x
    /\ b' = [b EXCEPT ![p] = FALSE]
    /\ S' = [S EXCEPT ![p] = {}]

Restart(p) ==
    ProcessSetup(p)

Next == 
    \/ \E p \in 1..N : 
        \/ /\ ~b[p] /\ x # y
           /\ b' = [b EXCEPT ![p] = TRUE]
           /\ S' = [S EXCEPT ![p] = (S[p] \cup {x}) \ {y}]
        \/ /\ b[p] /\ ~(y \in S[p])
           /\ Retry(p)
        \/ /\ y = p
           /\ Restart(p)

Spec == 
    Init /\ [][Next]_<<x, y, b, S>> /\ WF_next(<<x, y, b, S>>)

MutualExclusion ==
    /\ \A p1, p2 \in 1..N : 
        \/ ~(b[p1] /\ b[p2])
        \/ (p1 = p2)
        
Liveness ==
    <>[](\E p \in 1..N : y = p)

THEOREM Spec => []MutualExclusion

THEOREM Spec => Liveness
================================================================================