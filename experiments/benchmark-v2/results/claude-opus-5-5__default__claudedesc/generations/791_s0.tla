-------------------------------- MODULE MCKVS --------------------------------
(***************************************************************************)
(* Model-checking configuration wrapper for the KeyValueStore spec.        *)
(* The constants, variables, Init, Next, Spec, invariants and liveness     *)
(* properties are all defined in the extended KeyValueStore module.        *)
(* This module only adds a symmetry set over transaction identifiers so    *)
(* TLC can treat states that differ only by a renaming of TxId values as   *)
(* equivalent.                                                             *)
(***************************************************************************)
EXTENDS KeyValueStore, TLC

\* All permutations of TxId are symmetric. Transaction ids are
\* interchangeable, so TLC can reduce the state space.
TxIdSymmetric == Permutations(TxId)

=============================================================================