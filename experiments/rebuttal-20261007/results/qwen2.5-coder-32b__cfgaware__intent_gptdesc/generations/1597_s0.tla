------------------------------- MODULE MutualExclusion -------------------------------

CONSTANTS N \* Number of processes

ASSUME N \in Nat /\ N > 0

VARIABLES 
    inFastDoorway, \* Global indicator that some process is in the fast doorway
    intentFlags    \* Array of per-process flags marking intent to enter critical section

\* Initial predicate: No process is in the fast doorway and all intent flags are cleared.
Init == /\ inFastDoorway = FALSE
        /\ intentFlags = <<FALSE>> ^ N

\* Next-state relation for a single process
NextProcess(p) ==
    LET 
        otherProcesses == {q \in 0..N-1 : q # p}
        allClear == \A q \in otherProcesses : ~intentFlags[q]
    IN
    \/ /\ inFastDoorway = FALSE
       /\ intentFlags[p] = FALSE
       /\ \/ /\ intentFlags' = [intentFlags EXCEPT ![p] = TRUE]
              /\ inFastDoorway' = TRUE
          \/ /\ allClear
             /\ intentFlags' = [intentFlags EXCEPT ![p] = FALSE]
             /\ inFastDoorway' = FALSE
    \/ /\ inFastDoorway = TRUE
       /\ intentFlags[p] = TRUE
       /\ \/ /\ intentFlags' = [intentFlags EXCEPT ![p] = FALSE]
              /\ inFastDoorway' = FALSE
          \/ /\ allClear
             /\ intentFlags' = [intentFlags EXCEPT ![p] = FALSE]
             /\ inFastDoorway' = FALSE

\* Next-state relation for the system
Next ==
    \E p \in 0..N-1 : NextProcess(p)

\* Specification: Initial state and next-state relation
Spec == Init /\ [][Next]_<<inFastDoorway, intentFlags>>

\* Invariant: Mutual exclusion (at most one process in critical section)
Invariant ==
    \/ ~inFastDoorway
    \/ \E p \in 0..N-1 : intentFlags[p] /\ (\A q \in 0..N-1 : q # p => ~intentFlags[q])

\* Liveness: Weak fairness for each process's actions
Liveness ==
    WF_next(<<inFastDoorway, intentFlags>>, {p \in 0..N-1 : NextProcess(p)})

=============================================================================