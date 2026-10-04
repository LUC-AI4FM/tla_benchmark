--------------------------- MODULE TwoPhaseCommit ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS RM

VARIABLES rmState

vars == <<rmState>>

RMStates == {"working", "prepared", "committed", "aborted"}

TypeOK ==
    rmState \in [RM -> RMStates]

Init ==
    rmState = [r \in RM |-> "working"]

Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

CanCommit ==
    \A r \in RM : rmState[r] \in {"prepared", "committed"}

CanAbort ==
    \E r \in RM : rmState[r] \in {"working", "aborted"}

DecideCommit(r) ==
    /\ rmState[r] = "prepared"
    /\ CanCommit
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ CanAbort
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Decide(r) ==
    \/ DecideCommit(r)
    \/ DecideAbort(r)

Next ==
    \E r \in RM :
        \/ Prepare(r)
        \/ Decide(r)

Fairness ==
    \A r \in RM :
        /\ WF_vars(Prepare(r))
        /\ WF_vars(Decide(r))

Spec ==
    Init /\ [][Next]_vars /\ Fairness

Consistency ==
    ~(\E r1, r2 \in RM : rmState[r1] = "committed" /\ rmState[r2] = "aborted")

AllCommitted ==
    \A r \in RM : rmState[r] = "committed"

AllAborted ==
    \A r \in RM : rmState[r] = "aborted"

Terminated ==
    \A r \in RM : rmState[r] \in {"committed", "aborted"}

EventuallyTerminated ==
    <>Terminated

ConsistentTermination ==
    [](Terminated => (AllCommitted \/ AllAborted))

=============================================================================