------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals
CONSTANTS N

VARIABLES forks, state
vars == <<forks, state>>

RightFork(i) == i
LeftFork(i) == (i - 1) Mod N

(* Initial state: all forks free and all philosophers thinking *)
Init ==
  /\ forks = [i \in 0..N-1 |-> 0]
  /\ state = [i \in 0..N-1 |-> "Think"]

(* Actions for philosopher i *)
ThinkToFirst(i) ==
  IF i = 0 THEN
      /\ state[i] = "Think"
      /\ forks[LeftFork(i)] = 0
      /\ forks'[LeftFork(i)] = 1
      /\ state'[i] = "Left"
  ELSE
      /\ state[i] = "Think"
      /\ forks[RightFork(i)] = 0
      /\ forks'[RightFork(i)] = 1
      /\ state'[i] = "Right"

FirstToSecond(i) ==
  IF i = 0 THEN
      /\ state[i] = "Left"
      /\ state'[i] = "Eat"
  ELSE
      /\ state[i] = "Right"
      /\ forks[LeftFork(i)] = 0
      /\ forks'[LeftFork(i)] = 1
      /\ state'[i] = "Left"

EatToRelease(i) ==
      /\ state[i] = "Eat"
      /\ forks[LeftFork(i)]' = 0
      /\ forks[RightFork(i)]' = 0
      /\ state'[i] = "Think"

Next_i == ThinkToFirst(i) \/ FirstToSecond(i) \/ EatToRelease(i)

(* Next-state relation: one philosopher performs an action *)
Next == \E i \in 0..N-1 : Next_i

(* Safety invariant: at most one philosopher may eat at a time *)
Inv_MutualExclusion ==
  LET eatingIndices == {i \in 0..N-1 | state[i] = "Eat"} IN
    CARD(eatingIndices) <= 1

(* Liveness property: every philosopher eventually eats infinitely often *)
StarvationFreedom == \A i \in 0..N-1 : []( <> (state[i] = "Eat") )

Spec ==
  Init
  /\ [][Next]_vars
  /\ Inv_MutualExclusion
  /\ StarvationFreedom
  /\ (\A i \in 0..N-1 : Fairness(Next_i))

=============================================================================