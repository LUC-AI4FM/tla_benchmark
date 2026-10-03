------------------------------ MODULE MCSpecMultiNodeReadsAlt ------------------------------
EXTENDS Naturals, Sequences

(*--------------------------------------------------------------------
  Variables used by the specification
--------------------------------------------------------------------*)
VARIABLES ledgerBranches, history

(*--------------------------------------------------------------------
  Constants (placeholder values)
--------------------------------------------------------------------*)
nodes == {"node1", "node2"}

vars == {ledgerBranches, history}

(*--------------------------------------------------------------------
  Placeholder for the imported action.
  In a real system this would be defined in an external module and
  imported here.  For the purposes of this specification we provide
  a trivial definition that satisfies the syntax requirements.
--------------------------------------------------------------------*)
MCNextMultiNodeReadsAction ==
  /\ TRUE

(*--------------------------------------------------------------------
  Alternative initial state: two transactions are already committed.
--------------------------------------------------------------------*)
AltInit ==
  /\ ledgerBranches = [n \in nodes |-> []]
  /\ history = << 
        [txId |-> 1, status |-> "committed", response |-> "ok"],
        [txId |-> 2, status |-> "committed", response |-> "ok"]
     >>

(*--------------------------------------------------------------------
  Temporal specification that starts from the alternative initial state
  and evolves according to MCNextMultiNodeReadsAction using stuttering.
--------------------------------------------------------------------*)
MCSpecMultiNodeReadsAlt ==
  /\ AltInit
  /\ [][MCNextMultiNodeReadsAction]_vars

=============================================================================