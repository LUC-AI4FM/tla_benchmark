------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, S

Init == 
    /\ x = 0
    /\ y = 0
    /\ b = [p \in 1..N -> FALSE]
    /\ S = [p \in 1..N -> {}]

Next ==
    \/ \E p \in 1..N : 
        (\* Label A *)
        /\ ~b[p]
        /\ x = 0
        /\ y = 0
        /\ b' = [b EXCEPT ![p] = TRUE]
        /\ S' = [S EXCEPT ![p] = {}]
        /\ UNCHANGED <<x, y>>
    \/ \E p \in 1..N : 
        (\* Label B *)
        /\ b[p]
        /\ x = 0
        /\ y = 0
        /\ x' = p
        /\ S' = [S EXCEPT ![p] = {}]
        /\ UNCHANGED <<b, y>>
    \/ \E p \in 1..N : 
        (\* Label C *)
        /\ b[p]
        /\ x # 0
        /\ x # p
        /\ ~(\E q \in S[x]: q # p)
        /\ S' = [S EXCEPT ![p] = S[x] \cup {x}]
        /\ UNCHANGED <<b, x, y>>
    \/ \E p \in 1..N : 
        (\* Label D *)
        /\ b[p]
        /\ x # 0
        /\ x # p
        /\ (\E q \in S[x]: q = p)
        /\ y' = p
        /\ UNCHANGED <<b, x, S>>
    \/ \E p \in 1..N : 
        (\* Label E *)
        /\ b[p]
        /\ y = p
        /\ b' = [b EXCEPT ![p] = FALSE]
        /\ UNCHANGED <<x, y, S>>
    \/ \E p \in 1..N : 
        (\* Label F *)
        /\ ~b[p]
        /\ x = p
        /\ y = p
        /\ x' = 0
        /\ y' = 0
        /\ UNCHANGED <<b, S>>

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b, S>>
    /\ WF_next(Next)

MutualExclusion == 
    \A p1, p2 \in 1..N : p1 # p2 => ~(\E s \in S[p1]: s = p2) \/ ~(\E s \in S[p2]: s = p1)

Liveness ==
    <>[] (\E p \in 1..N: x = p /\ y = p)

=============================================================================