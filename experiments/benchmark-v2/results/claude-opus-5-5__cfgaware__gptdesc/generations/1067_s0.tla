---------------------- MODULE SyncTerminationDetection ----------------------
(***************************************************************************)
(* Abstract specification of termination detection in a ring with          *)
(* synchronous communication. Each node is active or inactive, and a       *)
(* boolean flag records whether global termination has been detected.      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES
  active,               \* activation status of nodes
  terminationDetected   \* has termination been detected?

vars == <<active, terminationDetected>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in BOOLEAN

terminated == \A n \in Node : ~ active[n]

---------------------------------------------------------------------------

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in {FALSE, terminated}

(* An active node terminates. *)
Terminate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ terminationDetected' \in {terminationDetected, terminated'}

(* An active node i wakes up an inactive node j (synchronous message). *)
Wakeup(i, j) ==
  /\ active[i]
  /\ ~ active[j]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED terminationDetected

(* Termination is detected when all nodes are inactive. *)
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

(* Termination is only detected when it has actually occurred. *)
TDCorrect == terminationDetected => terminated

(* Once all nodes are inactive, they remain inactive. *)
Quiescence == [](terminated => []terminated)

(* If the system terminates, termination is eventually detected. *)
Liveness == terminated ~> terminationDetected

=============================================================================