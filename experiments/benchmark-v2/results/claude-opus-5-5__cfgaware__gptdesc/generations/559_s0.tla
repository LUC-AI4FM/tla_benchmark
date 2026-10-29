------------------------------ MODULE MCPaxosCommit ------------------------------
(***************************************************************************)
(* Model-checking wrapper around the Paxos Commit specification.           *)
(*                                                                         *)
(* The names required by the configuration (PCSpec, RM, Acceptor,          *)
(* Majority, Ballot, PCTypeOK) are all defined in module PaxosCommit and   *)
(* are imported here through EXTENDS.                                      *)
(*                                                                         *)
(* Module TCommit is instantiated as TCommitSpec. Its constant RM and its  *)
(* variable rmState are implicitly substituted by the identically named    *)
(* constant and variable of PaxosCommit.                                   *)
(***************************************************************************)
EXTENDS PaxosCommit

TCommitSpec == INSTANCE TCommit

TCommitSpecProperty == TCommitSpec!TCSpec

THEOREM PCSpec => TCommitSpecProperty
=============================================================================