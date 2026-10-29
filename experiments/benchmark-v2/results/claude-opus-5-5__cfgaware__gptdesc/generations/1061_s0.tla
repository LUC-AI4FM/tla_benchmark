------------------------------- MODULE APSyncTerminationDetection -------------------------------
(***************************************************************************)
(* Wrapper that attaches Apalache type annotations to the variables and    *)
(* constant of SyncTerminationDetection. The definitions of the            *)
(* synchronous termination detection specification are given inline so    *)
(* that this module is self-contained.                                     *)
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

TDCorrect == terminationDetected => terminated

Stable == [](terminationDetected => []terminated)

Liveness == terminated ~> terminationDetected

=============================================================================