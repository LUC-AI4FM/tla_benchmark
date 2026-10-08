------------------------------- MODULE MutualExclusionLock -------------------------------

CONSTANTS NumProcesses \* Number of processes (at least 2)

VARIABLES lock, states \* lock is either "locked" or "unlocked"
                       \* states[p] is one of {"non-critical", "trying", "critical", "releasing"} for each process p

\* Define the set of all processes
PROCESSES == 1..NumProcesses

\* Initial predicate: lock is unlocked and all processes are in non-critical state
Init == /\ lock = "unlocked"
        /\ \A p \in PROCESSES : states[p] = "non-critical"

\* TypeOK: ensures that the lock and each process's state have valid values
TypeOK == /\ lock \in {"locked", "unlocked"}
          /\ \A p \in PROCESSES : states[p] \in {"non-critical", "trying", "critical", "releasing"}

\* LockInv: ensures lock consistency
LockInv == /\ (\E p \in PROCESSES : states[p] = "critical" \/ states[p] = "releasing") => lock = "locked"
           /\ (\A p \in PROCESSES : states[p] \notin {"critical", "releasing"}) => lock = "unlocked"

\* MutualExclusion: ensures that at most one process is in the critical section
MutualExclusion == \/ \A p, q \in PROCESSES : p # q => states[p] # "critical" \/ states[q] # "critical"
                   \/ \A p \in PROCESSES : states[p] = "critical" => (\A q \in PROCESSES : q # p => states[q] \notin {"critical", "releasing"})

\* Next: defines the possible state transitions
Next ==
    \/ /\ \E p \in PROCESSES : states[p] = "non-critical"
       /\ \E q \in PROCESSES : states[q] = "non-critical" /\ q # p
       /\ lock = "unlocked"
       /\ /\ [][p \in PROCESSES |-> IF states[p] = "non-critical" THEN "trying" ELSE states[p]]
    \/ /\ \E p \in PROCESSES : states[p] = "trying"
       /\ lock = "unlocked"
       /\ /\ [][p \in PROCESSES |-> IF states[p] = "trying" THEN "critical" ELSE states[p]]
          /\ lock' = "locked"
    \/ /\ \E p \in PROCESSES : states[p] = "critical"
       /\ /\ [][p \in PROCESSES |-> IF states[p] = "critical" THEN "releasing" ELSE states[p]]
    \/ /\ \E p \in PROCESSES : states[p] = "releasing"
       /\ /\ [][p \in PROCESSES |-> IF states[p] = "releasing" THEN "non-critical" ELSE states[p]]
          /\ lock' = "unlocked"

\* Spec: the complete specification
Spec == Init /\ [][Next]_<<states, lock>> /\ WF_next(<<states, lock>>)

=============================================================================