------------------------------- MODULE FischerMutex -------------------------------

CONSTANTS N \* Number of processes
CONSTANTS Delta \* First delay constant
CONSTANTS Epsilon \* Second delay constant

VARIABLES x, timers \* Shared variable and per-process timers

\* Initialization predicate
Init == /\ x = 0
        /\ timers = [p \in 1..N -> 0]

\* Process actions
Next ==
    \/ \E p \in 1..N : 
        (/\ timers[p] > 0
         /\ timers' = [timers EXCEPT ![p] = timers[p] - 1]
         /\ x' = x
        )
    \/ \E p \in 1..N :
        (/\ timers[p] = 0
         /\ x = 0
         /\ timers' = [timers EXCEPT ![p] = Delta]
         /\ x' = p
        )
    \/ \E p \in 1..N :
        (/\ timers[p] = 0
         /\ x = p
         /\ timers' = [timers EXCEPT ![p] = Epsilon]
         /\ x' = x
        )
    \/ \E p \in 1..N :
        (/\ timers[p] = 0
         /\ x = p
         /\ timers' = timers
         /\ x' = 0
        )

\* Specification of the system behavior
Spec ==
    Init /\ [][Next]_<<x, timers>>

\* Invariant: Mutual exclusion
Invariant == \A p1, p2 \in 1..N : \/ p1 # p2 \/ (p1 = p2 => x # p1)

\* Liveness property: Some process is in the critical section infinitely often
Liveness ==
    <>[](\E p \in 1..N : timers[p] = 0 /\ x = p)

=============================================================================