---------------------------- MODULE MCKVsnap ----------------------------
(***************************************************************************)
(* TLC-specific wrapper around the KVsnap specification.                   *)
(*                                                                         *)
(* This module defines no variables, Init, Next or Spec of its own.        *)
(* They all come from KVsnap: its constants (Key, TxId, NoVal, ...), its   *)
(* variables (store, ...), and its Init, Next and Spec, together with any  *)
(* invariants, fairness conditions and liveness properties it declares.    *)
(*                                                                         *)
(* This module adds only derived operators for model checking:             *)
(*   - TxIdSymmetric : a symmetry set over transaction identifiers.        *)
(*   - DebugInv      : a debugging invariant that uses TLC's execution     *)
(*                     level.                                              *)
(***************************************************************************)
EXTENDS KVsnap, TLC

(***************************************************************************)
(* Symmetry reduction over transaction identifiers.                        *)
(***************************************************************************)
TxIdSymmetric == Permutations(TxId)

(***************************************************************************)
(* Depth threshold above which the debugging check is enforced.            *)
(***************************************************************************)
DebugLevelThreshold == 10

(***************************************************************************)
(* Debugging invariant. Once the current behavior is deeper than the       *)
(* threshold (as reported by TLCGet("level")), it asserts that no two      *)
(* distinct keys in the store hold distinct non-NoVal values. Violating    *)
(* it makes TLC print a trace that reaches such a state.                   *)
(***************************************************************************)
DebugInv ==
    TLCGet("level") > DebugLevelThreshold =>
        ~ \E k1, k2 \in Key :
            /\ k1 # k2
            /\ store[k1] # NoVal
            /\ store[k2] # NoVal
            /\ store[k1] # store[k2]

=============================================================================