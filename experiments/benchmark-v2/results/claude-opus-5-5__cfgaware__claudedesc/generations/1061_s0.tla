---------------------- MODULE APSyncTerminationDetection ----------------------
(***************************************************************************)
(* Type-annotated wrapper of the synchronous termination detection        *)
(* specification for the Apalache model checker. The definitions of the   *)
(* original SyncTerminationDetection module are given inline here, so     *)
(* this module does not depend on an external file. It defines the same   *)
(* behaviour as the original module.                                      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Int;
    N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES
    \* @type: Int -> Bool;
    active,
    \* @type: Bool;
    terminationDetected

Node == 0 .. N-1

vars == <<active, terminationDetected>>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in BOOLEAN

terminated == \A n \in Node : ~ active[n]

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in {FALSE, terminated}

Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ terminationDetected' \in {terminationDetected, terminated'}

Wakeup(i, j) ==
    /\ active[i]
    /\ ~ active[j]
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ UNCHANGED terminationDetected

DetectTermination ==
    /\ terminated
    /\ ~ terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED active

Next ==
    \/ DetectTermination
    \/ \E i \in Node : Terminate(i)
    \/ \E i, j \in Node : Wakeup(i, j)

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

TDCorrect == terminationDetected => terminated

Stable == [](terminated => []terminated)

Live == terminated ~> terminationDetected
==============================================================================