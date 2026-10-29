---------------------------- MODULE MCReadersWriters ----------------------------
(***************************************************************************)
(* Model-checking module for the ReadersWriters specification.             *)
(* Init, Next, Spec, the safety invariants and the liveness properties are *)
(* all inherited from the extended module ReadersWriters. Redefining them  *)
(* here would cause a multiple-definition error in SANY.                   *)
(***************************************************************************)
EXTENDS ReadersWriters, TLC

n == 3

(***************************************************************************)
(* Notes on violated invariants (comments only, not TLA+ definitions):     *)
(*                                                                         *)
(*   - An invariant requiring that the waiting queue is always empty is    *)
(*     violated as soon as an actor attempts to read or write while the    *)
(*     resource is busy.                                                   *)
(*                                                                         *)
(*   - An invariant requiring that there is never more than one reader is  *)
(*     violated, because multiple readers may legally hold the resource    *)
(*     at the same time.                                                   *)
(*                                                                         *)
(*   - An invariant requiring that readers and writers are never both      *)
(*     waiting is violated, because readers and writers can be queued      *)
(*     together while the resource is in use.                              *)
(***************************************************************************)

=============================================================================