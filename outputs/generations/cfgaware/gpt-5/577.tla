---- MODULE MCSpecMultiNodeReadsAlt ----
EXTENDS Naturals, Sequences, TLC

(*
  Alternative initial state for a multi-node reads model.
  Two transactions t1 and t2 are already committed, as reflected in both
  the initialized ledger branches and the pre-populated history entries.
*)

CONSTANTS
(*
  Placeholder for the imported next-state action from the base model.
  In an integrated setup, this is expected to be supplied by the base spec
  or via configuration/definition override.
*)
  \* MCNextMultiNodeReadsAction is used below in the temporal spec.
  \* If not overridden, we default it to a stuttering action definition.
\* none

VARIABLES
  ledgerBranches,
  history

vars == << ledgerBranches, history >>

(*
  Basic universe used to shape the alternative initial state.
  These are concrete for the alternative init; they can be adapted if needed.
*)
Nodes == {"n1", "n2", "n3"}
Txns  == {"t1", "t2"}

(*
  Default (local) definition of the next-state action to ensure the module
  type-checks and parses standalone. In an integrated environment, this
  definition can be overridden by the base model's MCNextMultiNodeReadsAction.
*)
MCNextMultiNodeReadsAction == UNCHANGED vars

(*
  Alternative initial predicate:
  - Every node’s ledger branch already contains the two committed txns t1 and t2.
  - History is pre-populated with response and committed-status records for both txns.
*)
MCInitMultiNodeReadsAlt ==
  /\ ledgerBranches = [ n \in Nodes |-> << "t1", "t2" >> ]
  /\ history =
     <<
       [ type |-> "response",  node |-> "n1", txn |-> "t1", value |-> "ok" ],
       [ type |-> "committed",               txn |-> "t1"                  ],
       [ type |-> "response",  node |-> "n2", txn |-> "t2", value |-> "ok" ],
       [ type |-> "committed",               txn |-> "t2"                  ]
     >>

(*
  Temporal specification starting from the alternative initial state and
  evolving according to MCNextMultiNodeReadsAction with standard stuttering.
*)
MCSpecMultiNodeReadsAlt ==
  MCInitMultiNodeReadsAlt /\ [][MCNextMultiNodeReadsAction]_vars

====