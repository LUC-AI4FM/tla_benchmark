---------------------------- MODULE TwoPhaseCommit ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS RM

VARIABLES rmState

vars == <<rmState>>

RMStates == {"working", "prepared", "committed", "aborted"}

TypeOK == rmState \in [RM -> RMStates]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] /= "committed"

Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) ==
    /\ rmState[r] = "prepared"
    /\ canCommit
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ notCommitted
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Decide(r) == DecideCommit(r) \/ DecideAbort(r)

Init ==
    rmState = [r \in RM |-> "working"]

Next ==
    \E r \in RM : Prepare(r) \/ Decide(r)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Consistency ==
    ~(\E r1, r2 \in RM : rmState[r1] = "committed" /\ rmState[r2] = "aborted")

AllCommitted == \A r \in RM : rmState[r] = "committed"
AllAborted == \A r \in RM : rmState[r] = "aborted"

EventualDecision == <>(AllCommitted \/ AllAborted)

=============================================================================