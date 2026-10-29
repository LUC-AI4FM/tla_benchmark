---------------------------- MODULE MCPaxosCommit ----------------------------
(***************************************************************************)
(* A small model-checking wrapper around the Paxos Commit specification.  *)
(* It extends PaxosCommit, instantiates the Transaction Commit spec, and   *)
(* asserts that Paxos Commit implements Transaction Commit.                *)
(***************************************************************************)
EXTENDS PaxosCommit

(***************************************************************************)
(* The constants (RM, Ballot, Acceptor, Majority) and the variables        *)
(* (rmState, aState, msgs) are inherited from PaxosCommit.  TCommit's      *)
(* constant RM and variable rmState are substituted implicitly by the      *)
(* identically named PaxosCommit symbols.                                  *)
(***************************************************************************)
TCommitSpec == INSTANCE TCommit

TCommitSpecProperty == TCommitSpec!TCSpec

(***************************************************************************)
(* Aliases for the model checker.                                          *)
(***************************************************************************)
Init == PCInit

Next == PCNext

Spec == PCSpec

(***************************************************************************)
(* Safety invariants.                                                      *)
(***************************************************************************)
TypeInvariant == PCTypeOK

ConsistencyInvariant == TCommitSpec!TCConsistent

(***************************************************************************)
(* Paxos Commit implements Transaction Commit.                             *)
(***************************************************************************)
THEOREM PCSpec => TCommitSpecProperty
=============================================================================