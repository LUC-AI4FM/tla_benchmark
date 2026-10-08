MODULE FastMutex
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES x, y, b, S, pc

(* ------------------------------------------------------------------ *)
(* Types and initial state                                            *)
(* ------------------------------------------------------------------ *)

TypeInvariant ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [1..N -> BOOLEAN]
  /\ S \in [1..N -> SUBSET 1..N]
  /\ pc \in [1..N -> {"start","setx","checky","wait","critical","exit"}]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ S = [i \in 1..N |-> {}]
  /\ pc = [i \in 1..N |-> "start"]

(* ------------------------------------------------------------------ *)
(* Per‑process actions                                               *)
(* ------------------------------------------------------------------ *)

Start(i) ==
  /\ pc[i] = "start"
  /\ pc' = [pc EXCEPT ![i] = "setx"]
  /\ UNCHANGED <<x, y, b, S>>

SetX(i) ==
  /\ pc[i] = "setx"
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = "checky"]
  /\ UNCHANGED <<y, b, S>>

CheckY(i) ==
  /\ pc[i] = "checky"
  /\ IF y = 0 THEN y' = i ELSE y' = 0
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED <<x, b, S>>

Wait(i) ==
  /\ pc[i] = "wait"
  /\ IF y = i THEN
        pc' = [pc EXCEPT ![i] = "critical"]
     ELSE
        pc' = [pc EXCEPT ![i] = "start"]
  /\ UNCHANGED <<x, y, b, S>>

Critical(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED <<x, y, b, S>>

Exit(i) ==
  /\ pc[i] = "exit"
  /\ pc' = [pc EXCEPT ![i] = "start"]
  /\ UNCHANGED <<x, y, b, S>>

Next ==
  \E i \in 1..N :
    Start(i) \/ SetX(i) \/ CheckY(i) \/ Wait(i) \/ Critical(i) \/ Exit(i)

(* ------------------------------------------------------------------ *)
(* Safety invariant: no two processes in the critical section        *)
(* ------------------------------------------------------------------ *)

NoConcurrentCS ==
  [] ~(EXISTS i, j \in 1..N :
          i # j /\ pc[i] = "critical" /\ pc[j] = "critical")

(* ------------------------------------------------------------------ *)
(* Liveness property: infinitely often some process is in CS         *)
(* ------------------------------------------------------------------ *)

SomeInCS ==
  <> (EXISTS i \in 1..N : pc[i] = "critical")

(* ------------------------------------------------------------------ *)
(* Specification                                                     *)
(* ------------------------------------------------------------------ *)

Spec == Init /\ [][Next]_vars /\ WF_1(Next)

THEOREM NoConcurrentCS IMPLIES Spec
THEOREM SomeInCS

===============================================================================