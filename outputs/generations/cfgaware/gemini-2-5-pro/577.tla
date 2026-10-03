---- MODULE MCSpecMultiNodeReadsAlt ----
EXTENDS MCMultiNodeReads, TLC, Sequences

(*
This specification defines an alternative initial state where two transactions
are already committed. This is useful for model checking scenarios that start
from a non-empty ledger. The history variable is pre-populated with response
and committed-status records for these two transactions.
*)

MCInitAlt ==
    /\ ledger = <<t1, t2>>
    /\ branches = [n \in Nodes |-> <<t1, t2>>]
    /\ history = << [ type      |-> "response",
                      txn       |-> t1,
                      responses |-> [n \in Nodes |-> TRUE] ],
                   [ type   |-> "committed",
                     txn    |-> t1,
                     status |-> "committed" ],
                   [ type      |-> "response",
                      txn       |-> t2,
                      responses |-> [n \in Nodes |-> TRUE] ],
                   [ type   |-> "committed",
                     txn    |-> t2,
                     status |-> "committed" ] >>
    /\ pc = [n \in Nodes |-> "Done"]

MCSpecMultiNodeReadsAlt == MCInitAlt /\ [][MCNextMultiNodeReadsAction]_vars

=============================================================================