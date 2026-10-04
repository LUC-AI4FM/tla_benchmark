---------------------------- MODULE TwoPhaseCommit ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    RM  \* The set of resource managers

VARIABLES
    rmState  \* rmState[r] is the state of resource manager r

vars == <<rmState>>

\* The set of possible states for a resource manager
RMStates == {"working", "prepared", "committed", "aborted"}

\* Type correctness invariant
TypeOK ==
    rmState \in [RM -> RMStates]

\* Initial state: all RMs are in the "working" state
Init ==
    rmState = [r \in RM |-> "working"]

\* A working RM can prepare to commit
Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

\* A working RM can decide to abort unilaterally
DecideAbort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

\* A prepared RM can decide to commit only if all RMs are prepared or committed
\* (no RM has aborted and all have at least prepared)
DecideCommit(r) ==
    /\ rmState[r] = "prepared"
    /\ \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

\* Combined Decide action for RM r
Decide(r) ==
    \/ DecideAbort(r)
    \/ DecideCommit(r)

\* Next-state relation: disjunction of all RM actions
Next ==
    \E r \in RM :
        \/ Prepare(r)
        \/ Decide(r)

\* Consistency invariant: no two RMs can be in conflicting final states
\* (one committed and one aborted)
Consistency ==
    ~(\E r1, r2 \in RM : rmState[r1] = "committed" /\ rmState[r2] = "aborted")

\* Alternative formulation of consistency
NoConflictingDecisions ==
    \/ \A r \in RM : rmState[r] /= "committed"
    \/ \A r \in RM : rmState[r] /= "aborted"

\* An RM can only commit if all RMs have prepared
\* (Safety property: committed implies all prepared or committed)
CommitRequiresAllPrepared ==
    \A r \in RM :
        rmState[r] = "committed" =>
            \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

\* Fairness condition: weak fairness on all actions
Fairness ==
    \A r \in RM :
        /\ WF_vars(Prepare(r))
        /\ WF_vars(Decide(r))

\* Complete specification with fairness
Spec ==
    Init /\ [][Next]_vars /\ Fairness

\* Liveness property: eventually all RMs reach a terminal state (committed or aborted)
\* if the system keeps making progress
AllTerminate ==
    <>(\A r \in RM : rmState[r] \in {"committed", "aborted"})

\* Liveness property: if all RMs prepare, eventually all commit
AllPreparedLeadsToAllCommitted ==
    (\A r \in RM : rmState[r] = "prepared") ~> (\A r \in RM : rmState[r] = "committed")

=============================================================================