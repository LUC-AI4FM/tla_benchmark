MODULE DiningPhilosophers
EXTENDS Naturals, Sequences, TLC, Fairness

CONSTANT N \in Nat

VARIABLES pc, sem

(* Helper definitions *)
PhiloIds == 0 .. N-1
Forks    == 0 .. N-1
States   == {"Thinking", "TryRight", "TryLeft", "Eating"}

Right(i) == i
Left(i)  == (i - 1 + N) % N

vars == <<pc, sem>>

(* Initial state *)
Init ==
  /\ pc \in [PhiloIds -> States]
  /\ sem \in [Forks -> 0 .. N]
  /\ \A i \in PhiloIds: pc[i] = "Thinking"
  /\ \A f \in Forks: sem[f] = 0

(* Actions for philosophers > 0 *)
PickRight(i) ==
  /\ i \in PhiloIds
  /\ i # 0
  /\ pc[i] = "Thinking"
  /\ sem[Right(i)] = 0
  /\ pc'   = [pc EXCEPT ![i] = "TryLeft"]
  /\ sem'  = [sem EXCEPT ![Right(i)] = i+1]

PickLeft(i) ==
  /\ i \in PhiloIds
  /\ i # 0
  /\ pc[i] = "TryLeft"
  /\ sem[Left(i)] = 0
  /\ pc'   = [pc EXCEPT ![i] = "Eating"]
  /\ sem'  = [sem EXCEPT ![Left(i)] = i+1]

EatDone(i) ==
  /\ i \in PhiloIds
  /\ i # 0
  /\ pc[i] = "Eating"
  /\ pc'   = [pc EXCEPT ![i] = "Thinking"]
  /\ sem'  = [sem EXCEPT ![Right(i)] = 0, ![Left(i)] = 0]

(* Actions for philosopher 0 *)
PickLeft0 ==
  /\ pc[0] = "Thinking"
  /\ sem[Left(0)] = 0
  /\ pc'   = [pc EXCEPT ![0] = "TryRight"]
  /\ sem'  = [sem EXCEPT ![Left(0)] = 1]

PickRight0 ==
  /\ pc[0] = "TryRight"
  /\ sem[Right(0)] = 0
  /\ pc'   = [pc EXCEPT ![0] = "Eating"]
  /\ sem'  = [sem EXCEPT ![Right(0)] = 1]

EatDone0 ==
  /\ pc[0] = "Eating"
  /\ pc'   = [pc EXCEPT ![0] = "Thinking"]
  /\ sem'  = [sem EXCEPT ![Left(0)] = 0, ![Right(0)] = 0]

(* Next-state relation *)
Next ==
  \E i \in PhiloIds :
        (i # 0 /\ PickRight(i)) \/ (i # 0 /\ PickLeft(i)) \/ (i # 0 /\ EatDone(i))
   \/ (PickLeft0 \/ PickRight0 \/ EatDone0)

PHIL(i) ==
  (i # 0 /\ (PickRight(i) \/ PickLeft(i) \/ EatDone(i))) \/
  (i = 0 /\ (PickLeft0 \/ PickRight0 \/ EatDone0))

Fairness == \A i \in PhiloIds : WF_vars(PHIL(i), pc)

(* Safety invariant: adjacent philosophers never eat together *)
SafeAdjEat ==
  \A i \in PhiloIds :
    ~(pc[i] = "Eating" /\ (pc[Right(i)] = "Eating" \/ pc[Left(i)] = "Eating"))

Safety == SafeAdjEat

(* Liveness property: each philosopher eats infinitely often *)
InfinitelyOften(e) == [] <> e
Liveness ==
  \A i \in PhiloIds : InfinitelyOften(pc[i] = "Eating")

Spec == Init /\ [][Next]_vars /\ Fairness /\ Safety /\ Liveness

END MODULE