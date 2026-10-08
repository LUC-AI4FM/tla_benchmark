------------------------------- MODULE MutualExclusion -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES inFastDoorway, flags, criticalSectionProcess

Init == 
    /\ inFastDoorway = FALSE
    /\ flags = <<FALSE>> ^ N
    /\ criticalSectionProcess = << >>

Next ==
    \/ \E i \in 1..N : FastPath(i)
    \/ \E i \in 1..N : BackupPath(i)

FastPath(i) ==
    /\ inFastDoorway = FALSE
    /\ flags' = [flags EXCEPT ![i] = TRUE]
    /\ inFastDoorway' = TRUE
    /\ criticalSectionProcess' = <<i>>
    /\ UNCHANGED <<flags[j] \in 1..N \ {i}, inFastDoorway>>

BackupPath(i) ==
    LET waiting == \E j \in 1..(i-1) : flags[j]
        \/ (criticalSectionProcess # << >>)
    IN
    /\ flags[i]
    /\ waiting
    /\ flags' = [flags EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<inFastDoorway, criticalSectionProcess>>
    \/ /\ \A j \in 1..(i-1) : ~flags[j]
       /\ (criticalSectionProcess = << >>)
       /\ flags' = [flags EXCEPT ![i] = FALSE]
       /\ inFastDoorway' = TRUE
       /\ criticalSectionProcess' = <<i>>

Spec ==
    /\ Init
    /\ [][Next]_<<inFastDoorway, flags, criticalSectionProcess>>
    /\ <>(criticalSectionProcess # << >>)

\* Safety: Mutual Exclusion
MutualExclusion == \A i, j \in 1..N : i # j => \/ criticalSectionProcess = <<i>> => ~flags[j]
                   \/ criticalSectionProcess = <<j>> => ~flags[i]

\* Liveness: Weak Fairness for each process's actions
WF_FastPath ==
    /\ WF_<<FastPath(i) \in 1..N>>_<<inFastDoorway, flags, criticalSectionProcess>>
    /\ WF_<<BackupPath(i) \in 1..N>>_<<inFastDoorway, flags, criticalSectionProcess>>

\* Liveness: Eventually some process enters the critical section
Liveness == <>(criticalSectionProcess # << >>)

=============================================================================