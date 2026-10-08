MODULE DiningPhilosophers
EXTENDS Naturals, Integers, TLC

CONSTANTS N, NONE

(* Fork indices and philosopher indices are 0..N-1 *)
\* Right fork of philosopher i is fork i
RIGHT(i) == i
\* Left fork of philosopher i is the previous fork in the ring
LEFT(i) == (i - 1 + N) MOD N

(* States a philosopher can be in *)
THINKING    == "thinking"
HUNGRY_RIGHT== "hungerR"
HUNGRY_LEFT == "hungerL"
EATING      == "eating"

VARIABLES pc, sem
vars == <<pc, sem>>

Init ==
  /\ pc = [i \in 0..N-1 |-> THINKING]
  /\ sem = [f \in 0..N-1 |-> NONE]

(* Actions for philosophers i > 0 *)
PickRight(i) ==
  /\ pc[i] = THINKING
  /\ sem[RIGHT(i)] = NONE
  /\ pc'   = [pc EXCEPT ![i] = HUNGRY_RIGHT]
  /\ sem'  = [sem EXCEPT ![RIGHT(i)] = i]

PickLeft(i) ==
  /\ pc[i] = HUNGRY_RIGHT
  /\ sem[LEFT(i)] = NONE
  /\ pc'   = [pc EXCEPT ![i] = HUNGRY_LEFT]
  /\ sem'  = [sem EXCEPT ![LEFT(i)] = i]

EatStart(i) ==
  /\ pc[i] \in {HUNGRY_RIGHT, HUNGRY_LEFT}
  /\ sem[RIGHT(i)] = i
  /\ sem[LEFT(i)]  = i
  /\ pc'   = [pc EXCEPT ![i] = EATING]
  /\ UNCHANGED sem

FinishEating(i) ==
  /\ pc[i] = EATING
  /\ sem[RIGHT(i)] = i
  /\ sem[LEFT(i)]  = i
  /\ pc'   = [pc EXCEPT ![i] = THINKING]
  /\ sem'  = [sem EXCEPT ![RIGHT(i)] = NONE, ![LEFT(i)] = NONE]

(* Actions for philosopher 0 (opposite order) *)
PickLeft0 ==
  /\ pc[0] = THINKING
  /\ sem[LEFT(0)] = NONE
  /\ pc'   = [pc EXCEPT ![0] = HUNGRY_LEFT]
  /\ sem'  = [sem EXCEPT ![LEFT(0)] = 0]

PickRight0 ==
  /\ pc[0] = HUNGRY_LEFT
  /\ sem[RIGHT(0)] = NONE
  /\ pc'   = [pc EXCEPT ![0] = HUNGRY_RIGHT]
  /\ sem'  = [sem EXCEPT ![RIGHT(0)] = 0]

EatStart0 ==
  /\ pc[0] \in {HUNGRY_RIGHT, HUNGRY_LEFT}
  /\ sem[RIGHT(0)] = 0
  /\ sem[LEFT(0)]  = 0
  /\ pc'   = [pc EXCEPT ![0] = EATING]
  /\ UNCHANGED sem

FinishEating0 ==
  /\ pc[0] = EATING
  /\ sem[RIGHT(0)] = 0
  /\ sem[LEFT(0)]  = 0
  /\ pc'   = [pc EXCEPT ![0] = THINKING]
  /\ sem'  = [sem EXCEPT ![RIGHT(0)] = NONE, ![LEFT(0)] = NONE]

Next ==
  \E i \in 0..N-1 :
    ((i > 0) /\ (PickRight(i) \/ PickLeft(i) \/ EatStart(i) \/ FinishEating(i))) \/
    ((i = 0) /\ (PickLeft0 \/ PickRight0 \/ EatStart0 \/ FinishEating0))

(* Fairness for each philosopher *)
Action(i) ==
   ((i > 0) /\ (PickRight(i) \/ PickLeft(i) \/ EatStart(i) \/ FinishEating(i))) \/
   ((i = 0) /\ (PickLeft0 \/ PickRight0 \/ EatStart0 \/ FinishEating0))

Fairness == \A i \in 0..N-1 : WF/strong(Action(i))

Spec ==
  Init
  /\ [][Next]_vars
  /\ Fairness

(* Safety invariant: no two adjacent philosophers eat together *)
NoAdjEating ==
  \A i \in 0..N-1 :
    ~((pc[i] = EATING) /\ (pc[(i + 1) MOD N] = EATING))

THEOREM SafetyInvariant == NoAdjEating

(* Liveness property: each philosopher eats infinitely often *)
NoStarvation ==
  \A i \in 0..N-1 : <>[](pc[i] = EATING)

THEOREM LivenessProperty == NoStarvation
===============================================================================