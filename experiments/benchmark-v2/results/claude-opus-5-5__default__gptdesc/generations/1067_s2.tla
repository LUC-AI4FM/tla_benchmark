------------------------- MODULE SyncTerminationDetection -------------------------
(***************************************************************************)
(* Abstract specification of the termination-detection problem for a     *)
(* ring of nodes with synchronous communication. Each node is either      *)
(* active or inactive. A boolean flag records whether global termination  *)
(* has been detected.                                                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES
    active,               \* active[n] is TRUE iff node n is active
    terminationDetected   \* has global termination been detected?

vars == << active, terminationDetected >>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in BOOLEAN

\* All nodes are inactive.
terminated == \A n \in Node : ~ active[n]

---------------------------------------------------------------------------

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in {FALSE, terminated}

\* An active node i terminates (becomes inactive).
\* Detection may or may not happen at the same step.
Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ terminationDetected' \in {terminationDetected, terminated'}

\* An active node i wakes up another node j (synchronous communication).
Wakeup(i, j) ==
    /\ active[i]
    /\ ~ active[j]
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ UNCHANGED terminationDetected

\* Termination is detected once all nodes are inactive.
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

---------------------------------------------------------------------------
(* Properties *)

\* Safety: termination is only detected when all nodes are inactive.
TerminationDetection == terminationDetected => terminated

\* Once all nodes are inactive, they remain inactive forever.
Quiescence == [](terminated => []terminated)

\* Liveness: if the system terminates, termination is eventually detected.
Liveness == terminated ~> terminationDetected

\* Once detected, detection remains set.
StableDetection == [](terminationDetected => []terminationDetected)

THEOREM Spec => []TypeOK
THEOREM Spec => []TerminationDetection
THEOREM Spec => Quiescence
THEOREM Spec => Liveness
==============================================================================