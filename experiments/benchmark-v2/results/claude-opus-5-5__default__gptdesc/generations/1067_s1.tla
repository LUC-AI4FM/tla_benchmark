---------------------- MODULE SyncTerminationDetection ----------------------
(***************************************************************************)
(* Abstract specification of termination detection in a ring with         *)
(* synchronous communication. Each node is either active or inactive, and *)
(* a flag records whether global termination has been detected.           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES
  active,              \* activation status of each node
  terminationDetected  \* has global termination been detected?

vars == << active, terminationDetected >>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in BOOLEAN

terminated == \A n \in Node : ~ active[n]

---------------------------------------------------------------------------
Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in {FALSE, terminated}

(* An active node may terminate (become inactive). *)
Terminate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ terminationDetected' \in {terminationDetected, terminated'}

(* An active node i wakes up node j (synchronous communication). *)
Wakeup(i, j) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED terminationDetected

(* Detection of global termination. *)
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
(* Correctness: termination is only detected once it has occurred. *)
TerminationDetection == terminationDetected => terminated

(* Liveness: termination is eventually detected. *)
Liveness == terminated ~> terminationDetected

(* Quiescence: once the system has terminated, it remains terminated. *)
Quiescence == [](terminated => []terminated)

THEOREM Spec => []TypeOK
THEOREM Spec => []TerminationDetection
THEOREM Spec => Liveness
THEOREM Spec => Quiescence
=============================================================================