MODULE DiningPhilosophers
EXTENDS Naturals, Sequences, TLC

CONSTANT N \in Nat

VARIABLES forks, philoState, Requests

(* Helper definitions *)
LeftNeighbor(i) == IF i = 0 THEN N-1 ELSE i - 1
RightNeighbor(i) == (i + 1) MOD N

(* Initial state *)
Init ==
  /\ forks = [i \in 0..N-1 |-> [owner |-> i, clean |-> FALSE]]
  /\ philoState = [i \in 0..N-1 |-> "Thinking"]
  /\ Requests = [i \in 0..N-1 |-> {}]

(* Actions *)
Think(i) ==
  /\ philoState[i] = "Thinking"
  /\ philoState' = [philoState EXCEPT ![i] = "Hungry"]

Eat(i) ==
  /\ philoState[i] = "Hungry"
  /\ forks[i].owner = i
  /\ forks[LeftNeighbor(i)].owner = i
  /\ forks[i].clean = TRUE
  /\ forks[LeftNeighbor(i)].clean = TRUE
  /\ philoState' = [philoState EXCEPT ![i] = "Eating"]
  /\ forks' = [forks EXCEPT 
                ![i] = [owner |-> i, clean |-> FALSE],
                ![LeftNeighbor(i)] = [owner |-> i, clean |-> FALSE]]

FinishEating(i) ==
  /\ philoState[i] = "Eating"
  /\ philoState' = [philoState EXCEPT ![i] = "Thinking"]

RequestLeftFork(i) ==
  /\ philoState[i] = "Hungry"
  /\ forks[i].owner # i
  /\ Requests' = [Requests EXCEPT 
                   ![forks[i].owner] = Requests[forks[i].owner] \cup {i}]

RequestRightFork(i) ==
  /\ philoState[i] = "Hungry"
  /\ forks[LeftNeighbor(i)].owner # i
  /\ Requests' = [Requests EXCEPT 
                   ![forks[LeftNeighbor(i)].owner] = Requests[forks[LeftNeighbor(i)].owner] \cup {i}]

PassFork(i) ==
  LET p == forks[i].owner
      q == IF p = i THEN RightNeighbor(i) ELSE i
  IN
    /\ forks[i].clean = FALSE
    /\ q \in Requests[p]
    /\ forks' = [forks EXCEPT ![i] = [owner |-> q, clean |-> TRUE]]
    /\ Requests' = [Requests EXCEPT ![p] = Requests[p] \ {q}]

Next ==
  \E i \in 0..N-1 :
      (Think(i)
       \/ Eat(i)
       \/ FinishEating(i)
       \/ RequestLeftFork(i)
       \/ RequestRightFork(i)
       \/ PassFork(i))

vars == <<forks, philoState, Requests>>

(* Type correctness invariant *)
TypeInvariant ==
  /\ forks \in [0..N-1 -> [owner : 0..N-1, clean : BOOLEAN]]
  /\ philoState \in [0..N-1 -> {"Thinking", "Hungry", "Eating"}]
  /\ Requests \in [0..N-1 -> SUBSET 0..N-1]
  /\ \A i \in 0..N-1: forks[i].owner \in {i, LeftNeighbor(i)}
  /\ \A i \in 0..N-1: philoState[i] \in {"Thinking", "Hungry", "Eating"}
  /\ \A i \in 0..N-1: Requests[i] \subseteq {LeftNeighbor(i), RightNeighbor(i)}

(* Mutual exclusion invariant *)
MutualExclusion ==
  \A i \in 0..N-1 : ~(philoState[i] = "Eating" /\ philoState[RightNeighbor(i)] = "Eating")

(* Liveness property: no starvation *)
NoStarvation ==
  \A i \in 0..N-1 : (philoState[i] = "Hungry") => <> (philoState[i] = "Eating")

Spec == Init /\ [][Next]_vars
SpecWithFairness == Spec /\ Fair(Next) /\ TypeInvariant /\ MutualExclusion

THEOREM NoStarvationIsSatisfied ==
  SpecWithFairness => NoStarvation

(* End of module *)