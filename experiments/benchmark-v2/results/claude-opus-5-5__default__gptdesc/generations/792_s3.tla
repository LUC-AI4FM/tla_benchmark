---------------------------- MODULE MCKVsnap ----------------------------
(***************************************************************************)
(* TLC-specific wrapper around KVsnap. This module defines no variables,  *)
(* transition relation, or temporal specification of its own. Init, Next, *)
(* Spec, the constants (Key, TxId, NoVal), and the variables (including   *)
(* store) all come from KVsnap. This module only adds operators for       *)
(* symmetry reduction and debugging during model checking.                *)
(***************************************************************************)
EXTENDS KVsnap, TLC

\* Symmetry reduction over transaction identifiers.
TxIdSymmetric == Permutations(TxId)

\* Execution-level threshold for the debugging invariant.
LevelThreshold == 10

\* Debugging invariant: past the threshold level, no two distinct keys
\* hold distinct non-NoVal values. TLC reports a violation, with a trace,
\* once such a state is reached beyond the threshold.
DebugInv ==
    TLCGet("level") > LevelThreshold =>
        ~ \E k1, k2 \in Key :
              /\ k1 # k2
              /\ store[k1] # NoVal
              /\ store[k2] # NoVal
              /\ store[k1] # store[k2]
=============================================================================