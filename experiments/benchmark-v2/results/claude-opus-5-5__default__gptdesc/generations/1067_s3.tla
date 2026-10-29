---------------------------- MODULE TerminationDetection ----------------------------
(***************************************************************************)
(* Abstract specification of termination detection in a ring with         *)
(* synchronous communication. Each node is either active or inactive, and  *)
(* a boolean flag records whether global termination has been detected.    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES
  active,               \* active[n] is TRUE iff node n is active
  terminationDetected   \* TRUE iff global termination has been detected

vars == <<active, terminationDetected>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in BOOLEAN

terminated == \A n \in Node : ~ active[n]

---------------------------------------------------------------------------
Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in {FALSE, terminated}

\* An active node i terminates (becomes inactive).
\* Termination may be detected immediately if this makes all nodes inactive.
Terminate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ terminationDetected' \in {terminationDetected, terminated'}

\* An active node i wakes up node j (synchronous message passing).
Wakeup(i, j) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED terminationDetected

\* Separate detection step: set the flag once all nodes are inactive.
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
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* Safety: termination is detected only if all nodes are inactive.
TDCorrect == terminationDetected => terminated

\* Quiescence: once all nodes are inactive, they remain inactive.
Quiescence == [](terminated => []terminated)

\* Liveness: if the system terminates, termination is eventually detected.
Liveness == terminated ~> terminationDetected

\* Once detected, detection is stable.
StableDetection == [](terminationDetected => []terminationDetected)

THEOREM Spec => []TypeOK
THEOREM Spec => []TDCorrect
THEOREM Spec => Quiescence
THEOREM Spec => Liveness
=============================================================================