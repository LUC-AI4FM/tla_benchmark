---------------------------- MODULE TwoPCwithBTM ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS RM,          \* the set of resource managers
          RMMAYFAIL,   \* whether resource managers may crash (fail-stop)
          TMMAYFAIL    \* whether the primary transaction manager may crash

VARIABLES rmState,     \* local state of each resource manager
          tmState,     \* state of the primary transaction manager
          btmState     \* state of the backup transaction manager

vars == <<rmState, tmState, btmState>>

RMStates  == {"working", "prepared", "committed", "aborted", "failed"}
TMStates  == {"init", "commit", "abort", "hidden"}
BTMStates == {"init", "commit", "abort"}

TypeOK ==
    /\ rmState \in [RM -> RMStates]
    /\ tmState \in TMStates
    /\ btmState \in BTMStates

-----------------------------------------------------------------------------
(* Decision predicates *)

\* Primary TM: commit only if every RM is prepared.
canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

\* Primary TM: abort if some RM aborted or failed.
canAbort == \E rm \in RM : rmState[rm] \in {"aborted", "failed"}

\* Backup TM: commit is safe if all RMs are prepared, or if some RM has
\* already committed (which reveals that the primary decided commit).
bCanCommit ==
    \/ \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
    \/ \E rm \in RM : rmState[rm] = "committed"

\* Backup TM: abort is safe if some RM aborted/failed and nobody committed.
bCanAbort ==
    /\ \E rm \in RM : rmState[rm] \in {"aborted", "failed"}
    /\ ~\E rm \in RM : rmState[rm] = "committed"

decidedCommit == tmState = "commit" \/ btmState = "commit"
decidedAbort  == tmState = "abort"  \/ btmState = "abort"

-----------------------------------------------------------------------------
Init ==
    /\ rmState  = [rm \in RM |-> "working"]
    /\ tmState  = "init"
    /\ btmState = "init"

(* Resource manager actions *)

RMPrepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    /\ UNCHANGED <<tmState, btmState>>

RMChooseAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED <<tmState, btmState>>

RMRcvCommit(rm) ==
    /\ rmState[rm] = "prepared"
    /\ decidedCommit
    /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
    /\ UNCHANGED <<tmState, btmState>>

RMRcvAbort(rm) ==
    /\ rmState[rm] = "prepared"
    /\ decidedAbort
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED <<tmState, btmState>>

RMFail(rm) ==
    /\ RMMAYFAIL
    /\ rmState[rm] \in {"working", "prepared"}
    /\ rmState' = [rmState EXCEPT ![rm] = "failed"]
    /\ UNCHANGED <<tmState, btmState>>

RMProgress(rm) ==
    \/ RMPrepare(rm)
    \/ RMRcvCommit(rm)
    \/ RMRcvAbort(rm)

RMAct(rm) ==
    \/ RMProgress(rm)
    \/ RMChooseAbort(rm)
    \/ RMFail(rm)

(* Primary transaction manager actions *)

TMCommit ==
    /\ tmState = "init"
    /\ canCommit
    /\ tmState' = "commit"
    /\ UNCHANGED <<rmState, btmState>>

TMAbort ==
    /\ tmState = "init"
    /\ canAbort
    /\ tmState' = "abort"
    /\ UNCHANGED <<rmState, btmState>>

TMDecide == TMCommit \/ TMAbort

\* The primary may crash after having made its decision.
TMFail ==
    /\ TMMAYFAIL
    /\ tmState \in {"commit", "abort"}
    /\ tmState' = "hidden"
    /\ UNCHANGED <<rmState, btmState>>

(* Backup transaction manager actions: take over when primary is hidden *)

BTMCommit ==
    /\ tmState = "hidden"
    /\ btmState = "init"
    /\ bCanCommit
    /\ btmState' = "commit"
    /\ UNCHANGED <<rmState, tmState>>

BTMAbort ==
    /\ tmState = "hidden"
    /\ btmState = "init"
    /\ bCanAbort
    /\ btmState' = "abort"
    /\ UNCHANGED <<rmState, tmState>>

BTMDecide == BTMCommit \/ BTMAbort

-----------------------------------------------------------------------------
Next ==
    \/ \E rm \in RM : RMAct(rm)
    \/ TMDecide
    \/ TMFail
    \/ BTMDecide

Fairness ==
    /\ \A rm \in RM : WF_vars(RMProgress(rm))
    /\ WF_vars(TMDecide)
    /\ WF_vars(BTMDecide)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

\* No two non-failed RMs reach conflicting outcomes.
Consistency ==
    \A rm1, rm2 \in RM :
        ~(rmState[rm1] = "committed" /\ rmState[rm2] = "aborted")

\* Commit is never decided in the presence of an aborted RM.
Validity ==
    decidedCommit => \A rm \in RM : rmState[rm] # "aborted"

\* Primary and backup never disagree.
DecisionAgreement ==
    ~(decidedCommit /\ decidedAbort)

\* Every RM eventually reaches a terminal local state.
Termination ==
    <>(\A rm \in RM : rmState[rm] \in {"committed", "aborted", "failed"})

\* The coordinator role (primary or backup) eventually completes a decision.
DecisionTermination ==
    <>(decidedCommit \/ decidedAbort)

=============================================================================