--------------------- MODULE APSyncTerminationDetection ---------------------
(***************************************************************************)
(* Thin wrapper around SyncTerminationDetection that attaches Apalache    *)
(* type annotations to its constant and variables without modifying the   *)
(* original specification. This module defines no algorithm steps,        *)
(* temporal properties or proofs of its own. It only declares typed       *)
(* parameters and links them to the underlying module. Init, Next and     *)
(* Spec are aliases of the definitions in the instantiated module.        *)
(***************************************************************************)
EXTENDS Integers

CONSTANT
    \* @type: Int;
    N

VARIABLES
    \* @type: Int -> Bool;
    active,
    \* @type: Bool;
    terminationDetected

STD == INSTANCE SyncTerminationDetection
            WITH N <- N,
                 active <- active,
                 terminationDetected <- terminationDetected

Init == STD!Init

Next == STD!Next

Spec == STD!Spec

=============================================================================