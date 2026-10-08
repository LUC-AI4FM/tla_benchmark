MODULE RingTermination
EXTENDS TemporalOperators, TLC

CONSTANTS Node

VARIABLES status, detected

(* The state of each node: TRUE = active, FALSE = inactive *)
statusType == [n \in Node |-> BOOLEAN]

(* Actions *)

Terminate(n) ==
  /\ n \in Node
  /\ status[n] = TRUE
  /\ status' = [status EXCEPT ![n] = FALSE]
  /\ UNCHANGED detected

WakeUp(m, n) ==
  /\ m \in Node
  /\ n \in Node
  /\ m # n
  /\ status[m] = TRUE
  /\ status[n] = FALSE
  /\ status' = [status EXCEPT ![n] = TRUE]
  /\ UNCHANGED detected

Detect ==
  /\ detected = FALSE
  /\ ∀n \in Node : status[n] = FALSE
  /\ detected' = TRUE
  /\ UNCHANGED status

Next ==
  ∃ n \in Node : Terminate(n)
  \/ ∃ m, n \in Node : (m # n) /\ WakeUp(m, n)
  \/ Detect

(* Initial condition *)
Init ==
  /\ ∀n \in Node : status[n] = TRUE
  /\ detected = FALSE

(* Type invariant *)
TypeOK ==
  /\ status ∈ [Node -> BOOLEAN]
  /\ detected ∈ BOOLEAN

(* Correctness invariant: if detection flag is set, all nodes are inactive *)
Correctness == ∀ n \in Node : (detected => status[n] = FALSE)

(* Quiescence property: after detection the system stays idle *)
Quiescence == Correctness

(* Liveness property: when all nodes become inactive, eventually detection occurs *)
Liveness1 == ∀ n \in Node : (status[n] = FALSE) => ◇ detected

detectAct == Detect

Spec ==
  Init
  /\ [][Next]_<<status, detected>>
  /\ WF_detectAct
  /\ TypeOK

===============================================================================