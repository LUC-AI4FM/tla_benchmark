---------------------------- MODULE MutualExclusionProtocol ----------------------------

CONSTANTS N \* Number of processes

VARIABLES 
    intent, \* Intent flags for each process
    owner   \* Owner indicator

\* Initial state: no process has expressed intent and no owner
defaultInitValue == <<[p \in 1..N -> FALSE], NULL>>

Init == /\ intent = [p \in 1..N -> FALSE]
        /\ owner = NULL

\* Process p expresses intent to enter critical section
ExpressIntent(p) == intent' = [intent EXCEPT ![p] = TRUE]

\* Process p tries a fast acquisition of the critical section
TryFastAcquire(p) ==
    \E q \in 1..N : (q # p /\ intent[q]) \/ owner /= NULL
        -> owner' = owner
        \/ /\ owner' = p
           /\ \A q \in 1..N \ {p} : intent'[q] = intent[q]

\* Process p withdraws its intent and waits for a window where others are not indicating interest
WithdrawAndWait(p) ==
    /\ intent' = [intent EXCEPT ![p] = FALSE]
    /\ owner' = owner

\* Process p exits the critical section, clears its intent, and releases ownership
ExitCritical(p) ==
    /\ intent' = [intent EXCEPT ![p] = FALSE]
    /\ owner' = NULL

\* Next state relation for a single process
NextProcess(p) ==
    \/ /\ ExpressIntent(p)
       /\ TryFastAcquire(p)
    \/ /\ \E q \in 1..N : (q # p /\ intent[q]) \/ owner /= NULL
       /\ WithdrawAndWait(p)
    \/ /\ owner = p
       /\ ExitCritical(p)

\* Next state relation for all processes
Next ==
    \E p \in 1..N : NextProcess(p) /\ \A q \in 1..N \ {p} : intent'[q] = intent[q]

Spec == Init /\ [][Next]_<<intent, owner>>

\* Mutual exclusion: at most one process can be in the critical section
MutualExclusion ==
    \/ owner = NULL
    \/ \A p, q \in 1..N : (p # q => owner /= p \/ owner /= q)

\* No process has expressed intent if it is not the owner
NoFalseIntent ==
    \A p \in 1..N : intent[p] => owner = p

Invariant == MutualExclusion /\ NoFalseIntent

\* Liveness: from any reachable state, some process will eventually enter the critical section
Liveness ==
    <>[] (\E p \in 1..N : owner = p)

=============================================================================