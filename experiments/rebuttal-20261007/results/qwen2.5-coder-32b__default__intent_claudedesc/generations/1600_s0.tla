------------------------------- MODULE FastMutex -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES turn, interested, flags, inCS

Init == 
    /\ turn = 0
    /\ interested = 0
    /\ flags = [p \in 1..N -> FALSE]
    /\ inCS = [p \in 1..N -> FALSE]

TryEntry(p) ==
    \/ /\ interested' = p
       /\ UNCHANGED <<turn, flags, inCS>>
    \/ /\ interested = p
       /\ turn' = p
       /\ UNCHANGED <<flags, inCS>>

FastPath(p) ==
    /\ interested = p
    /\ turn = p
    /\ \A q \in 1..N \ {p}: ~flags[q]
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ flags' = [flags EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<turn, interested>>

SlowPath(p) ==
    /\ interested = p
    /\ turn # p
    /\ \/ \E q \in 1..N \ {p}: flags[q]
       \/ turn # 0
    /\ flags' = [flags EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<turn, inCS>>

WaitForFlags(p) ==
    /\ interested = p
    /\ \A q \in 1..N \ {p}: ~flags[q]
    /\ UNCHANGED <<turn, inCS, flags>>

CheckTurn(p) ==
    /\ interested = p
    /\ turn = p
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<turn, flags>>

WaitForTurn(p) ==
    /\ interested = p
    /\ turn # p
    /\ UNCHANGED <<flags, inCS>>

ReleaseCS(p) ==
    /\ inCS[p]
    /\ turn' = 0
    /\ flags' = [flags EXCEPT ![p] = FALSE]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ interested' = 0

Next == 
    \E p \in 1..N: 
        \/ TryEntry(p)
        \/ FastPath(p)
        \/ SlowPath(p)
        \/ WaitForFlags(p)
        \/ CheckTurn(p)
        \/ WaitForTurn(p)
        \/ ReleaseCS(p)

Spec == 
    /\ Init
    /\ [][Next]_<<turn, interested, flags, inCS>>
    /\ WF_<<p \in 1..N >> TryEntry(p)

MutualExclusion ==
    \A p, q \in 1..N: p # q => ~[]<>(inCS[p] /\ inCS[q])

Liveness ==
    \A p \in 1..N: <>(\E i \in 1..N: inCS[i])

=============================================================================