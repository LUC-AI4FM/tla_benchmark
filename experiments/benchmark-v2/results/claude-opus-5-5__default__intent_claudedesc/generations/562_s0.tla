--------------------------- MODULE TCommit ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANT RM

VARIABLE rmState

vars == <<rmState>>

States == {"working", "prepared", "committed", "aborted"}

TypeOK == rmState \in [RM -> States]

Init == rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] # "committed"

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

Next == \E r \in RM : Prepare(r) \/ Decide(r)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

TCConsistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

(* Whenever any RM has committed, every RM is prepared or committed
   (no RM is still working or has aborted). *)
CommitSafetyInv ==
    (\E r \in RM : rmState[r] = "committed")
        => \A s \in RM : rmState[s] \in {"prepared", "committed"}

(* Action-level commit safety: a commit step occurs only when all
   participants were prepared or committed. *)
CommitSafety ==
    [][\A r \in RM :
          (rmState[r] # "committed" /\ rmState'[r] = "committed")
              => \A s \in RM : rmState[s] \in {"prepared", "committed"}]_vars

(* Action-level abort safety: an abort step occurs only when no
   participant has committed. *)
AbortSafety ==
    [][\A r \in RM :
          (rmState[r] # "aborted" /\ rmState'[r] = "aborted")
              => \A s \in RM : rmState[s] # "committed"]_vars

THEOREM Spec => [](TypeOK /\ TCConsistent /\ CommitSafetyInv)
THEOREM Spec => CommitSafety /\ AbortSafety
=============================================================================