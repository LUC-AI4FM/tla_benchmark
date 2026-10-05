-------------------------------- MODULE TwoPhaseCommit --------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS RM \* The set of resource managers

VARIABLES rmState \* rmState[r] is the state of resource manager r

TypeOK ==
    rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

Init ==
    rmState = [r \in RM |-> "working"]

\* RM r prepares to commit
Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

\* Check if all RMs are prepared (no RM is still working)
AllPrepared ==
    \A r \in RM : rmState[r] \in {"prepared", "committed"}

\* Check if any RM has aborted
SomeAborted ==
    \E r \in RM : rmState[r] = "aborted"

\* Check if any RM has committed
SomeCommitted ==
    \E r \in RM : rmState[r] = "committed"

\* RM r decides to commit
\* Can only commit if all RMs are prepared and none has aborted
DecideCommit(r) ==
    /\ rmState[r] = "prepared"
    /\ AllPrepared
    /\ ~SomeAborted
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

\* RM r decides to abort
\* Can abort from working or prepared state, but not if someone has already committed
DecideAbort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ ~SomeCommitted
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

\* The Decide action for RM r
Decide(r) ==
    \/ DecideCommit(r)
    \/ DecideAbort(r)

\* Next-state relation: disjunction of all RM actions
Next ==
    \E r \in RM :
        \/ Prepare(r)
        \/ Decide(r)

\* Fairness: weak fairness on all RM actions
Fairness ==
    \A r \in RM :
        /\ WF_rmState(Prepare(r))
        /\ WF_rmState(Decide(r))

\* The complete specification
Spec == Init /\ [][Next]_rmState /\ Fairness

\* Safety invariant: No two RMs can reach conflicting decisions
\* (one committed and one aborted)
Consistency ==
    ~(\E r1, r2 \in RM : rmState[r1] = "committed" /\ rmState[r2] = "aborted")

\* Combined invariant for type correctness and consistency
Invariant == TypeOK /\ Consistency

\* Liveness property: Eventually all RMs reach the same terminal state
\* Either all commit or all abort
AllCommitted == \A r \in RM : rmState[r] = "committed"
AllAborted == \A r \in RM : rmState[r] = "aborted"

Termination == <>(AllCommitted \/ AllAborted)

\* Agreement: If any RM commits, eventually all will commit
Agreement == \A r \in RM : (rmState[r] = "committed") => <>(AllCommitted)

================================================================================