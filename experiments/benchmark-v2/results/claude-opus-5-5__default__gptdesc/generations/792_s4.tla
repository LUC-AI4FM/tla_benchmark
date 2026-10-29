------------------------------ MODULE MCKVsnap ------------------------------
(***************************************************************************)
(* TLC-specific wrapper around the KVsnap specification.                   *)
(*                                                                         *)
(* This module defines no variables, Init, Next or Spec of its own.        *)
(* Those (Init, Next, Spec, store, Key, TxId, NoVal, ...) come from        *)
(* KVsnap through EXTENDS. Redefining them here would cause SANY           *)
(* multiple-definition errors. The module adds only derived operators      *)
(* for symmetry reduction and debugging under TLC.                         *)
(***************************************************************************)
EXTENDS KVsnap, TLC

(***************************************************************************)
(* Symmetry set over transaction identifiers, for TLC symmetry reduction.  *)
(***************************************************************************)
TxIdSymmetric == Permutations(TxId)

(***************************************************************************)
(* Execution depth threshold above which the debugging invariant is        *)
(* checked.                                                                *)
(***************************************************************************)
DebugLevelThreshold == 10

(***************************************************************************)
(* Debugging invariant. Once TLC's current execution level (the depth of   *)
(* the behavior) exceeds the threshold, it checks that no two distinct     *)
(* keys in the store hold distinct non-NoVal values. When TLC reports a    *)
(* violation, it produces a trace to an "interesting" state for            *)
(* inspection.                                                             *)
(***************************************************************************)
TLCDebugInv ==
    TLCGet("level") > DebugLevelThreshold =>
        ~ \E k1, k2 \in Key :
              /\ k1 # k2
              /\ store[k1] # NoVal
              /\ store[k2] # NoVal
              /\ store[k1] # store[k2]

=============================================================================