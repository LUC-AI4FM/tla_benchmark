------------------------------- MODULE MCTwoPhase -------------------------------
(***************************************************************************)
(* Model-checking wrapper for the two-phase commit protocol.  It defines  *)
(* the typing invariant for the resource-manager and transaction-manager   *)
(* state, imports the transaction-commit specification via INSTANCE, and   *)
(* states that two-phase commit implements transaction commit.             *)
(***************************************************************************)

    -------------------------- MODULE TCommit ------------------------------
    (***********************************************************************)
    (* The abstract transaction-commit specification.                      *)
    (***********************************************************************)
    CONSTANT RM
    VARIABLE rmState

    TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

    TCInit == rmState = [r \in RM |-> "working"]

    canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

    notCommitted == \A r \in RM : rmState[r] # "committed"

    Prepare(r) == /\ rmState[r] = "working"
                  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

    Decide(r) == \/ /\ rmState[r] = "prepared"
                    /\ canCommit
                    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
                 \/ /\ rmState[r] \in {"working", "prepared"}
                    /\ notCommitted
                    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

    TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

    TCConsistent == \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                                         /\ rmState[r2] = "committed"

    TCSpec == TCInit /\ [][TCNext]_rmState
    ========================================================================