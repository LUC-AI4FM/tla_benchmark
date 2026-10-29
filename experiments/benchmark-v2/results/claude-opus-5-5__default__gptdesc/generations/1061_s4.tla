---------------------- MODULE APSyncTerminationDetection ----------------------
(***************************************************************************)
(* Thin wrapper around SyncTerminationDetection that only attaches         *)
(* Apalache type annotations. It adds no algorithm steps, actions,         *)
(* temporal properties or proofs. It only aliases the definitions of the   *)
(* instantiated module so that tools can refer to them.                    *)
(***************************************************************************)
EXTENDS Naturals

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

vars == <<active, terminationDetected>>

Init   == STD!Init
Next   == STD!Next
Spec   == STD!Spec
TypeOK == STD!TypeOK
================================================================================