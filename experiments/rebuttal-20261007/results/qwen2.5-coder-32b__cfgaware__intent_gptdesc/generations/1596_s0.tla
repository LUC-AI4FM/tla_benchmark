---------------------------- MODULE FastMutualExclusion ----------------------------

CONSTANTS N \* Number of processes

VARIABLES 
    in_critical_section, \* Set of processes currently in critical section
    intent,              \* Array where intent[p] is TRUE if process p intends to enter CS
    waiting,             \* Array where waiting[p] is TRUE if process p is waiting for entry
    backoff_count        \* Array where backoff_count[p] counts retries for process p

\* Initialization predicate
Init == 
    /\ in_critical_section = {}
    /\ intent = [p \in 1..N -> FALSE]
    /\ waiting = [p \in 1..N -> FALSE]
    /\ backoff_count = [p \in 1..N -> 0]

\* Next-state relation for a single process
ProcessNext(p) ==
    LET 
        announce_intent == intent' = [intent EXCEPT ![p] = TRUE]
        probe_others == \A q \in (1..N) \ {p}: intent[q] => waiting[p]' = TRUE
        detect_contention == \E q \in (1..N) \ {p}: intent[q]
        backoff == 
            /\ waiting' = [waiting EXCEPT ![p] = FALSE]
            /\ intent' = [intent EXCEPT ![p] = FALSE]
            /\ backoff_count' = [backoff_count EXCEPT ![p] = backoff_count[p] + 1]
        enter_critical_section ==
            /\ in_critical_section' = in_critical_section \cup {p}
            /\ waiting' = [waiting EXCEPT ![p] = FALSE]
            /\ intent' = [intent EXCEPT ![p] = FALSE]
            /\ backoff_count' = [backoff_count EXCEPT ![p] = 0]
        leave_critical_section ==
            /\ in_critical_section' = in_critical_section \ {p}
    IN
    \/ /\ intent[p] = FALSE
       /\ announce_intent
       /\ probe_others
       /\ IF detect_contention THEN backoff ELSE enter_critical_section
    \/ /\ intent[p] = TRUE
       /\ waiting[p]
       /\ IF detect_contention THEN backoff ELSE enter_critical_section
    \/ /\ p \in in_critical_section
       /\ leave_critical_section

\* Next-state relation for all processes
Next ==
    \E p \in 1..N: ProcessNext(p)

\* Specification of the system behavior
Spec == Init /\ [][Next]_<<in_critical_section, intent, waiting, backoff_count>>

\* Invariant: mutual exclusion (at most one process in critical section)
Invariant ==
    \/ in_critical_section = {}
    \/ \A p, q \in 1..N: p # q => p \notin in_critical_section \/ q \notin in_critical_section

\* Liveness property: global eventual entry fairness
Liveness ==
    WF_next(ProcessNext)

=============================================================================