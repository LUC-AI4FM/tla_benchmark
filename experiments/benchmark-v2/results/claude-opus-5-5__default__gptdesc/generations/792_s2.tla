---------------------------- MODULE MCKVsnap ----------------------------
(***************************************************************************)
(* TLC-specific wrapper around KVsnap.                                     *)
(*                                                                         *)
(* CONSTANTS, VARIABLES, Init, Next, Spec and all invariants and           *)
(* properties are inherited from KVsnap through EXTENDS. This module adds  *)
(* no transition system, variables or temporal specification of its own.  *)
(* It only adds derived operators for symmetry reduction and debugging.    *)
(***************************************************************************)
EXTENDS KVsnap, TLC

(***************************************************************************)
(* Symmetry set over transaction identifiers. Use it in the TLC model      *)
(* configuration as:  SYMMETRY TxIdSymmetric                               *)
(***************************************************************************)
TxIdSymmetric == Permutations(TxId)

(***************************************************************************)
(* Debugging invariant. Above a given execution level (behavior depth),   *)
(* no two distinct keys may hold distinct non-NoVal values. A violation   *)
(* makes TLC print a deep trace in which such a state is reached. This is  *)
(* useful for confirming that the model reaches interesting states.       *)
(***************************************************************************)
DebugLevelThreshold == 10

SerializabilityDebug ==
    TLCGet("level") > DebugLevelThreshold =>
        \A k1, k2 \in Key :
            (k1 # k2 /\ store[k1] # NoVal /\ store[k2] # NoVal)
                => store[k1] = store[k2]

=============================================================================