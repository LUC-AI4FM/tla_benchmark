---------------------- MODULE APASyncTerminationDetection ----------------------
(***************************************************************************)
(* Thin wrapper around SyncTerminationDetection that only attaches         *)
(* Apalache type annotations. It does not change the original              *)
(* specification. It adds no algorithm steps, actions, temporal            *)
(* properties or proofs of its own. Init, Next and Spec are re-exported    *)
(* unchanged from the instantiated module.                                 *)
(***************************************************************************)

CONSTANT
    \* @type: Int;
    N

VARIABLES
    \* @type: Int -> Bool;
    active,
    \* @type: Bool;
    terminationDetected

STD == INSTANCE SyncTerminationDetection

\* Re-exported from the underlying specification, without modification.
Init == STD!Init

Next == STD!Next

Spec == STD!Spec

================================================================================