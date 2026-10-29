---------------------- MODULE APASyncTerminationDetection ----------------------
(***************************************************************************)
(* Type-annotated wrapper of SyncTerminationDetection for Apalache.        *)
(* The SyncTerminationDetection definitions are reproduced inline so that  *)
(* this module parses on its own. If SyncTerminationDetection.tla is       *)
(* available, all definitions below may be replaced by:                    *)
(*                                                                         *)
(*     INSTANCE SyncTerminationDetection                                   *)
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
    \/ \E i \in Node : Terminate(i)
    \/ \E i, j \in Node : Wakeup(i, j)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

(* Safety: termination is detected only if all nodes are inactive *)
TDCorrect == terminationDetected => terminated

(* Additional properties of the original specification *)
Quiescence == [](terminated => [] terminated)

Liveness == terminated ~> terminationDetected

THEOREM Spec => [](TypeOK /\ TDCorrect)
=============================================================================