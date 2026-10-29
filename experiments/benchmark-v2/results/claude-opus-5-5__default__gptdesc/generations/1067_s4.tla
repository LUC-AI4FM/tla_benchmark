------------------------------ MODULE TerminationDetection ------------------------------
(***************************************************************************)
(* Abstract specification of the termination-detection problem in a ring  *)
(* with synchronous communication.                                         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES
  active,      \* activation status of nodes
  terminationDetected

vars == << active, terminationDetected >>

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
     (* possibly (but not necessarily) detect termination if all nodes are inactive *)
  /\ terminationDetected' \in {terminationDetected, terminated'}

Wakeup(i,j) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED terminationDetected

DetectTermination ==
  /\ terminated
  /\ ~ terminationDetected
  /\ terminationDetected' = TRUE
  /\ UNCHANGED active

Next ==
  \/ \E i \in Node : Terminate(i)
  \/ \E i,j \in Node : Wakeup(i,j)
  \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------------------
(* Safety: termination is only detected when all nodes are inactive *)
TDCorrect == terminationDetected => terminated

(* Quiescence: once all nodes are inactive, they remain so *)
Quiescence == [](terminated => []terminated)

(* Liveness: termination is eventually detected *)
Liveness == terminated ~> terminationDetected

THEOREM Spec => []TypeOK
THEOREM Spec => []TDCorrect
THEOREM Spec => Quiescence
THEOREM Spec => Liveness
=========================================================================================