------------------------------- MODULE MCTwoPhase -------------------------------
(***************************************************************************)
(* Model-checking wrapper around the two-phase commit protocol.            *)
(*                                                                         *)
(* It defines:                                                             *)
(*   - TPTypeOK, the typing invariant for the resource-manager (RM) and    *)
(*     transaction-manager (TM) state.                                     *)
(*   - TC, an INSTANCE of the transaction-commit specification TCommit.    *)
(*   - A theorem stating that the two-phase commit specification implies  *)
(*     the transaction-commit specification TC!TCSpec.                     *)
(*                                                                         *)
(* The task required standalone SANY parsing. The external modules were    *)
(* therefore not available, so this file includes:                         *)
(*   - TCommit, as a nested submodule.                                     *)
(*   - The two-phase commit actions, Init, Next and Spec, written out in   *)
(*     this module.                                                        *)
(* This module adds no fault model beyond those definitions.               *)
(***************************************************************************)

    ------------------------------ MODULE TCommit ------------------------------
    (***********************************************************************)
    (* The abstract transaction-commit specification.                      *)
    (***********************************************************************)
    CONSTANT RM

    VARIABLE rmState

    TCTypeOK ==
        rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

    TCInit == rmState = [r \in RM |-> "working"]

    canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

    notCommitted == \A r \in RM : rmState[r] # "committed"

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

    TCConsistent ==
        \A r1, r2 \in RM :
            ~ /\ rmState[r1] = "aborted"
              /\ rmState[r2] = "committed"

    TCSpec == TCInit /\ [][TCNext]_rmState
    ============================================================================