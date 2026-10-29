------------------------------ MODULE TCommit ------------------------------
(***************************************************************************)
(* Specification of the transaction commit problem.  A set RM of resource  *)
(* managers must agree on whether to commit or abort a transaction.  Each  *)
(* RM starts in the "working" state.  It may then become "prepared" or     *)
(* "aborted".  An RM may commit only if every RM is prepared or committed. *)
(* An RM may abort only if no RM has committed.  Commit and abort are      *)
(* final decisions.                                                        *)
(***************************************************************************)
CONSTANT RM       \* The set of participating resource managers

VARIABLE rmState  \* rmState[r] is the state of resource manager r

\* A concrete set of three resource managers, for model checking.
RMVal == {"r1", "r2", "r3"}

-----------------------------------------------------------------------------
TCTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant.                                      *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit ==
  (*************************************************************************)
  (* Initially every RM is working.                                       *)
  (*************************************************************************)
  rmState = [r \in RM |-> "working"]

canCommit ==
  (*************************************************************************)
  (* True iff every RM is prepared or committed.                          *)
  (*************************************************************************)
  \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted ==
  (*************************************************************************)
  (* True iff no RM has committed.                                        *)
  (*************************************************************************)
  \A r \in RM : rmState[r] # "committed"

-----------------------------------------------------------------------------
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

TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

-----------------------------------------------------------------------------
TCConsistent ==
  (*************************************************************************)
  (* No RM has committed while another has aborted.                       *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

TCValidity ==
  (*************************************************************************)
  (* If some RM has committed, then no RM is still working or aborted.    *)
  (*************************************************************************)
  (\E r \in RM : rmState[r] = "committed") =>
      \A r \in RM : rmState[r] \in {"prepared", "committed"}

TCStability ==
  (*************************************************************************)
  (* Commit and abort decisions are irrevocable.                          *)
  (*************************************************************************)
  [][\A r \in RM :
        /\ rmState[r] = "committed" => rmState'[r] = "committed"
        /\ rmState[r] = "aborted"   => rmState'[r] = "aborted"]_rmState

TCSpec == TCInit /\ [][TCNext]_rmState

-----------------------------------------------------------------------------
THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================