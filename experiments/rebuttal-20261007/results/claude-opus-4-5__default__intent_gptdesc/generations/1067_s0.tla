---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

VARIABLES
    active,         \* active[i] = TRUE iff process i is active
    terminated      \* TRUE iff termination has been detected

vars == <<active, terminated>>

Procs == 1..N

\* All processes are inactive
AllInactive == \A i \in Procs : ~active[i]

\* Initial state: arbitrary active/inactive assignment, termination not yet detected
Init ==
    /\ active \in [Procs -> BOOLEAN]
    /\ terminated = FALSE

\* A process locally decides to become inactive (local termination)
LocalTerminate(i) ==
    /\ active[i] = TRUE
    /\ terminated = FALSE
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED terminated

\* An active process sends an activation to another process, potentially waking it up
Activate(i, j) ==
    /\ active[i] = TRUE
    /\ terminated = FALSE
    /\ i # j
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ UNCHANGED terminated

\* Termination detection event: can only occur when all processes are inactive
DetectTermination ==
    /\ terminated = FALSE
    /\ AllInactive
    /\ terminated' = TRUE
    /\ UNCHANGED active

\* Next state relation
Next ==
    \/ \E i \in Procs : LocalTerminate(i)
    \/ \E i, j \in Procs : Activate(i, j)
    \/ DetectTermination

\* Fairness: weak fairness on detection ensures it eventually happens when enabled
Fairness == WF_vars(DetectTermination)

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* ====================