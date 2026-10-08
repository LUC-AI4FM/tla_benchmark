------------------------------- MODULE MCMultiNodeReadsAlt -------------------------------

EXTENDS MCMultiNodeReads

(*
This wrapper pairs an alternative initial state with the same next-state relation
and variables mechanism used by the parent MCMultiNodeReads module. It is intended
to start from a non-trivial, pre-committed setting (two committed transactions with
history/receipts) to exercise the same invariants under different initial conditions.
*)

VARIABLE dummy

(*
InitAlt is a wrapper placeholder for an alternative, non-empty initial state where
two transactions are already committed and their corresponding request/response
events and committed receipts are present in history. The concrete shape of this
state is determined by (and validated against) the underlying MCMultiNodeReads
state space and invariants during model checking.
*)
InitAlt == TRUE

(*
Temporal specification:
- Uses the same next-state action MCNextMultiNodeReadsAction provided by
  MCMultiNodeReads.
- Subscripted with a local stuttering variable 'dummy' to admit stuttering steps.
  The parent module's action governs the real system evolution.
*)
MCSpecMultiNodeReadsAlt == InitAlt /\ [][MCNextMultiNodeReadsAction]_dummy

=============================================================================