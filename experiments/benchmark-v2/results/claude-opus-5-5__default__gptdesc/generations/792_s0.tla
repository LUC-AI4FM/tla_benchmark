---------------------------- MODULE MCKVsnap ----------------------------
(***************************************************************************)
(* TLC-specific wrapper around the KVsnap specification.                   *)
(*                                                                         *)
(* This module defines no transition system of its own. It adds no         *)
(* CONSTANTS, VARIABLES, Init, Next or Spec. All of these come from        *)
(* KVsnap through EXTENDS, including:                                      *)
(*   - the constants Key, TxId and NoVal                                   *)
(*   - the variable store                                                  *)
(*   - Init, Next, Spec and its fairness conditions                        *)
(*   - the safety invariants and liveness properties                       *)
(* This module only adds derived operators for symmetry reduction and      *)
(* debugging during model checking.                                        *)
(***************************************************************************)
EXTENDS KVsnap, TLC

---------------------------------------------------------------------------
(***************************************************************************)
(* Symmetry reduction: transaction identifiers are interchangeable.        *)
(***************************************************************************)
TxIdSymmetric == Permutations(TxId)

---------------------------------------------------------------------------
(***************************************************************************)
(* Debugging invariant.                                                    *)
(*                                                                         *)
(* Below the depth threshold it holds trivially. Above the threshold it    *)
(* checks that no two distinct keys hold distinct non-NoVal values.        *)
(*                                                                         *)
(* A violation makes TLC print a trace to a state where two different keys *)
(* hold two different real values. This helps confirm that such states are *)
(* reachable.                                                              *)
(***************************************************************************)
DebugLevelThreshold == 20

TerminateInvariant ==
    \/ TLCGet("level") < DebugLevelThreshold
    \/ ~ \E k1, k2 \in Key :
            /\ k1 # k2
            /\ store[k1] # NoVal
            /\ store[k2] # NoVal
            /\ store[k1] # store[k2]

=============================================================================