------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, j

Init == 
    /\ x = 0
    /\ y = 0
    /\ b = <<FALSE>> ^ N
    /\ j = [p \in 1..N -> 0]

ProcessAction(p) ==
    \/ /\ x = 0
       /\ y = 0
       /\ b' = [b EXCEPT ![p] = TRUE]
       /\ x' = p
       /\ UNCHANGED <<y, j>>
    \/ /\ x = p
       /\ \E q \in 1..N : q # p /\ b[q]
       /\ y' = p
       /\ UNCHANGED <<x, b, j[p]>>
    \/ /\ x = p
       /\ y = p
       /\ b' = [b EXCEPT ![p] = FALSE]
       /\ j' = [j EXCEPT ![p] = 0]
       /\ UNCHANGED <<x, y>>
    \/ /\ x # p
       /\ y = p
       /\ j[p]' = (j[p] + 1) % N
       /\ b' = [b EXCEPT ![p] = TRUE]
       /\ x' = p
       /\ UNCHANGED <<y, j[EXCEPT !p]>>
    \/ /\ x # p
       /\ y # p
       /\ j[p]' = (j[p] + 1) % N
       /\ b' = [b EXCEPT ![p] = TRUE]
       /\ x' = p
       /\ UNCHANGED <<y, j[EXCEPT !p]>>

Next ==
    \E p \in 1..N : ProcessAction(p)

Spec == 
    /\ Init
    /\ [][Next]_<<x, y, b, j>>
    /\ WF_<<x, y, b, j>> (ProcessAction)

MutualExclusion ==
    \/ x = 0
    \/ \A p1, p2 \in 1..N : p1 # p2 => ~b[p1] \/ ~b[p2]

Liveness ==
    <>[](\E p \in 1..N : x = p /\ y = p)

=============================================================================