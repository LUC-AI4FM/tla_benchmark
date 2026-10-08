--------------------------- MODULE DiningPhilosophers ---------------------------
EXTENDS Naturals, TLC

CONSTANTS N
CONST   THINKING  = 0
CONST   HUNGRY    = 1
CONST   GOTRIGHT  = 2
CONST   GOTLEFT   = 3
CONST   EATING    = 4

VARIABLES pc, sem

(* Helper functions for fork indices *)
LeftFork(i) == i
RightFork(i) == (i + 1) % N

(* Initial state *)
Init ==
  /\ pc \in [0..N-1 -> {THINKING, HUNGRY, GOTRIGHT, GOTLEFT, EATING}]
  /\ sem \in [0..N-1 -> BOOLEAN]
  /\ \A i \in 0..N-1 : pc[i] = THINKING
  /\ \A f \in 0..N-1 : sem[f] = TRUE

(* Actions for a philosopher i *)
ThinkToHungry(i) ==
  /\ pc[i] = THINKING
  /\ pc' = [pc EXCEPT ![i] = HUNGRY]
  /\ UNCHANGED <<sem>>

PickFirst(i) ==
  \/ (i = 0 /\ pc[i] = HUNGRY /\ sem[LeftFork(0)] = TRUE
      /\ pc' = [pc EXCEPT ![i] = GOTLEFT]
      /\ sem' = [sem EXCEPT ![LeftFork(i)] = FALSE])
  \/ (i > 0 /\ pc[i] = HUNGRY /\ sem[RightFork(i)] = TRUE
      /\ pc' = [pc EXCEPT ![i] = GOTRIGHT]
      /\ sem' = [sem EXCEPT ![RightFork(i)] = FALSE])

PickSecond(i) ==
  \/ (i = 0 /\ pc[i] = GOTLEFT /\ sem[RightFork(0)] = TRUE
      /\ pc' = [pc EXCEPT ![i] = EATING]
      /\ sem' = [sem EXCEPT ![RightFork(i)] = FALSE])
  \/ (i > 0 /\ pc[i] = GOTRIGHT /\ sem[LeftFork(i)] = TRUE
      /\ pc' = [pc EXCEPT ![i] = EATING]
      /\ sem' = [sem EXCEPT ![LeftFork(i)] = FALSE])

Release(i) ==
  /\ pc[i] = EATING
  /\ sem' = [sem EXCEPT ![RightFork(i)] = TRUE, ![LeftFork(i)] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = THINKING]

(* Set of all actions of philosopher i *)
Philo(i) == ThinkToHungry(i) \/ PickFirst(i) \/ PickSecond(i) \/ Release(i)

Next ==
  \E i \in 0..N-1 :
      (ThinkToHungry(i) \/ PickFirst(i) \/ PickSecond(i) \/ Release(i))

(* Safety invariant: adjacent philosophers do not eat simultaneously *)
SafeInvariant == \A i \in 0..N-1 : ~(pc[i] = EATING /\ pc[RightFork(i)] = EATING)

(* Liveness property: each philosopher eats infinitely often *)
StarvationFree ==
  \A i \in 0..N-1 : [](<>(pc[i] = EATING))

Spec == Init
        /\ [][Next]_<<pc, sem>>
        /\ ( \A i \in 0..N-1 : Fairness(Philo(i)) )

THEOREM SafetyInvariantThm == []SafeInvariant
THEOREM StarvationFreeThm == StarvationFree

=============================================================================