--------------------------- MODULE TCommit ---------------------------
(***************************************************************************)
(* Transaction commit protocol for distributed resource managers.          *)
(* Each resource manager (RM) reaches agreement with the others on whether *)
(* to commit or abort a transaction.                                        *)
(***************************************************************************)

CONSTANT RM          \* The set of participating resource managers

VARIABLE rmState     \* rmState[r] is the state of resource manager r

vars == << rmState >>

(***************************************************************************)
(* Type correctness: every RM is in one of the four allowed states.        *)
(***************************************************************************)
TCTypeOK ==
    rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

(***************************************************************************)
(* Initially, all resource managers are working.                           *)
(***************************************************************************)
TCInit ==
    rmState = [r \in RM |-> "working"]

(***************************************************************************)
(* An RM may commit only if every RM is prepared or committed.             *)
(***************************************************************************)
canCommit ==
    \A r \in RM : rmState[r] \in {"prepared", "committed"}

(***************************************************************************)
(* An RM may abort only if no RM has committed.                            *)
(***************************************************************************)
notCommitted ==
    \A r \in RM : rmState[r] # "committed"

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r) ==
    \/ /\ rmState[r] = "prepared"
       /\ canCommit
       /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    \/ /\ rmState[r] \in {"working", "prepared"}
       /\ notCommitted
       /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

DecideCommit(r) ==
    /\ rmState[r] = "prepared"
    /\ canCommit
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ notCommitted
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

(***************************************************************************)
(* Next-state relation: some RM nondeterministically takes one action.     *)
(***************************************************************************)
TCNext ==
    \E r \in RM : Prepare(r) \/ DecideCommit(r) \/ DecideAbort(r)

(***************************************************************************)
(* Consistency: no RM has committed while another has aborted.             *)
(* (Not declared as a model-checking invariant, but holds by construction.)*)
(***************************************************************************)
TCConsistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

(***************************************************************************)
(* Temporal specification: stuttering steps permitted, no fairness.        *)
(***************************************************************************)
TCSpec == TCInit /\ [][TCNext]_vars

Init == TCInit
Next == TCNext
Spec == TCSpec

=============================================================================