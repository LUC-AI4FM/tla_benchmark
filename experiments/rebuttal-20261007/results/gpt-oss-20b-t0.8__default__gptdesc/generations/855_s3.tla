MODULE PrisonersAndSwitches
EXTENDS Naturals

CONSTANTS N, Counter

VARIABLES SwitchA, SwitchB, Count, Visited, Usage

(* Type invariants *)
TypeInv == 
   /\ SwitchA \in BOOLEAN
   /\ SwitchB \in BOOLEAN
   /\ Count \in Nat
   /\ Count <= N-1
   /\ Visited \subseteq 1 .. N
   /\ Usage \in [j \in 1 .. N |-> Nat]
   /\ \A j \in 1 .. N : Usage[j] <= 2

(* Initial state *)
Init == 
   /\ SwitchA = FALSE
   /\ SwitchB = FALSE
   /\ Count = 0
   /\ Visited = {}
   /\ Usage = [j \in 1 .. N |-> 0]

(* Counter action *)
CounterAction(i) ==
   /\ i = Counter
   /\ SwitchA' = FALSE
   /\ Count' = IF SwitchA THEN Count + 1 ELSE Count
   /\ Visited' = Visited ∪ {i}
   /\ Usage' = Usage

(* Non-counter action *)
NonCounterAction(i) ==
   /\ i # Counter
   /\ Visited' = Visited ∪ {i}
   /\ Count' = Count
   /\ IF (Usage[i] < 2) /\ (SwitchA = FALSE) THEN
        /\ SwitchA' = TRUE
        /\ Usage' = [j \in 1 .. N |-> IF j = i THEN Usage[j] + 1 ELSE Usage[j]]
        /\ SwitchB' = SwitchB
     ELSE
        /\ SwitchA' = SwitchA
        /\ SwitchB' = NOT SwitchB
        /\ Usage' = Usage

(* General action for a selected prisoner *)
Action(i) ==
   IF i = Counter THEN CounterAction(i)
   ELSE NonCounterAction(i)

Next == ∃ i \in 1 .. N : Action(i)

Complete == Count = N-1 /\ Visited = {i \in 1 .. N}

Safety == Complete => Visited = {i \in 1 .. N}

Liveness == <> (Count = N-1)

Fairness == WF_vars i \in 1 .. N : Action(i)

Spec == Init /\ [][Next]_vars /\ Fairness /\ TypeInv /\ Safety /\ Liveness

END MODULE