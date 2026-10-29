---------------------- MODULE APSyncTerminationDetection ----------------------
(***************************************************************************)
(* Wrapper around SyncTerminationDetection that adds Apalache type        *)
(* annotations without modifying the original specification.              *)
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

Init == STD!Init

Next == STD!Next

Spec == STD!Spec

=============================================================================