---------------------------- MODULE TerminationDetection ----------------------------
(***************************************************************************)
(* Abstract specification of termination detection for a ring of N nodes *)
(* that communicate synchronously. It serves as a reference specification *)
(* that concrete algorithms such as EWD840 can be shown to refine.        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES active, terminationDetected

vars == <<active, terminationDetected>>

(* Global termination: all nodes are inactive. *)
terminated == \A i \in Node : ~ active[i]

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in BOOLEAN

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in {FALSE, terminated}

(* An active node becomes inactive. Detection may happen at the same time. *)
Terminate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ terminationDetected' \in {terminationDetected, terminated'}

(* An active node i activates some node j. *)
Wakeup(i, j) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED terminationDetected

(* Termination is detected when all nodes are inactive. *)
DetectTermination ==
  /\ terminated
  /\ terminationDetected' = TRUE
  /\ UNCHANGED active

Next ==
  \/ \E i \in Node : Terminate(i)
  \/ \E i, j \in Node : Wakeup(i, j)
  \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------
(* Invariants *)

TDCorrect == terminationDetected => terminated

(* Temporal properties *)

Quiescence == [](terminated => []terminated)

Liveness == terminated ~> terminationDetected

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ TDCorrect)
THEOREM Spec => Quiescence /\ Liveness
=============================================================================