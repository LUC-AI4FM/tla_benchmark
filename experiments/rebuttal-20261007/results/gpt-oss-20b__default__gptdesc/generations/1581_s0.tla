MODULE DiningPhilosophers
EXTENDS Naturals, Sequences, TLC, Temporal

CONSTANT N

VARIABLES pc, sem

(* Helper functions *)
left(i) == (i - 1 + N) % N
right(i) == i

(* Initial state *)
Init ==
  /\ \A i \in 0..N-1 : sem[i] = TRUE
  /\ \A i \in 0..N-1 : pc[i] = "start"

(* Actions for philosophers > 0 *)
PickRight(i) ==
  /\ pc[i]="start"
  /\ sem[i] = TRUE
  /\ sem' = [sem EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "right"]

PickLeft(i) ==
  /\ pc[i]="right"
  /\ sem[left(i)] = TRUE
  /\ sem' = [sem EXCEPT ![left(i)] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "left"]

Eat(i) ==
  /\ pc[i]="left"
  /\ pc' = [pc EXCEPT ![i] = "eat"]
  /\ UNCHANGED << sem >>

Release(i) ==
  /\ pc[i]="eat"
  /\ sem' = [sem EXCEPT ![i] = TRUE, ![left(i)] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "start"]

(* Actions for philosopher 0 (opposite order) *)
PickLeftZero ==
  /\ pc[0]="start"
  /\ sem[left(0)] = TRUE
  /\ sem' = [sem EXCEPT ![left(0)] = FALSE]
  /\ pc' = [pc EXCEPT ![0] = "left"]

PickRightZero ==
  /\ pc[0]="left"
  /\ sem[right(0)] = TRUE
  /\ sem' = [sem EXCEPT ![right(0)] = FALSE]
  /\ pc' = [pc EXCEPT ![0] = "right"]

(* Next-state relation *)
Next ==
  \E i \in 1..N-1 :
    (PickRight(i) \/ PickLeft(i) \/ Eat(i) \/ Release(i))
  \/ (PickLeftZero \/ PickRightZero \/ Eat(0) \/ Release(0))

(* Action of a single philosopher *)
PhiloAction(i) ==
  IF i = 0 THEN
    PickLeftZero \/ PickRightZero \/ Eat(0) \/ Release(0)
  ELSE
    PickRight(i) \/ PickLeft(i) \/ Eat(i) \/ Release(i)

(* Safety invariant: adjacent philosophers do not eat simultaneously *)
NoAdjacentEat ==
  \A i,j \in 0..N-1 :
    (j = left(i) \/ j = right(i)) /\ i /= j
      => ~(pc[i] = "eat" /\ pc[j] = "eat")

(* Liveness property: each philosopher eats infinitely often *)
StarvationFreedom ==
  \A i \in 0..N-1 : []<>(pc[i] = "eat")

Spec == Init /\ [][Next]_vars
        /\ ( \A i \in 0..N-1 : WF_vars(PhiloAction(i)) )
        /\ NoAdjacentEat
        /\ StarvationFreedom

(* End of module *)