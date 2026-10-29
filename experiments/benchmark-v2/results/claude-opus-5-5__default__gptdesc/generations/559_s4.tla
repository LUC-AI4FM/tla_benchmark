---------------------------- MODULE MCPaxosCommit ----------------------------
(***************************************************************************)
(* A small model-checking wrapper around the Paxos Commit specification.  *)
(* It checks that Paxos Commit implements the Transaction Commit spec.    *)
(***************************************************************************)
EXTENDS PaxosCommit

TCommitSpec == INSTANCE TCommit

TCommitSpecProperty == TCommitSpec!TCSpec

THEOREM PCSpec => TCommitSpecProperty
=============================================================================