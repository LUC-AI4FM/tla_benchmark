------------------------------- MODULE FischerMutex -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, Delta, Epsilon

VARIABLES lock, timers, inCS

Init == /\ lock = 0
        /\ timers = [p \in 1..N -> 0]
        /\ inCS = {}

Next ==
    \/ \E p \in 1..N :
         /\ timers[p] = 0
         /\ lock = 0
         /\ ~ (p \in inCS)
         /\ /\ lock' = p
            /\ timers' = [timers EXCEPT ![p] = Delta]
            /\ inCS' = {p}
    \/ \E p \in 1..N :
         /\ p \in inCS
         /\ timers[p] > Epsilon
         /\ /\ timers' = [timers EXCEPT ![p] = timers[p] - 1]
            /\ UNCHANGED <<lock, inCS>>
    \/ \E p \in 1..N :
         /\ p \in inCS
         /\ timers[p] <= Epsilon
         /\ lock = p
         /\ /\ timers' = [timers EXCEPT ![p] = timers[p] - 1]
            /\ UNCHANGED <<lock, inCS>>
    \/ \E p \in 1..N :
         /\ p \in inCS
         /\ timers[p] <= Epsilon
         /\ lock # p
         /\ /\ lock' = 0
            /\ timers' = [timers EXCEPT ![p] = 0]
            /\ inCS' = {}
    \/ /\ \A p \in 1..N : timers[p] > 0
       /\ timers' = [p \in 1..N |-> timers[p] - 1]
       /\ UNCHANGED <<lock, inCS>>

Spec ==
    /\ Init
    /\ [][Next]_<<lock, timers, inCS>>
    /\ WF_<<lock, timers, inCS>>[Next]

MutualExclusion == \A p, q \in 1..N : p # q => ~ (p \in inCS) \/ ~ (q \in inCS)

Liveness ==
    \A p \in 1..N :
        <>[](p \in inCS)

THEOREM Spec => []MutualExclusion

THEOREM Spec => Liveness
=============================================================================