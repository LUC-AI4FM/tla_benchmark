------------------------------ MODULE Prisoners ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS N, InitialLampKnown, Counter
ASSUME Counter \in 1..N

VARIABLES lamp, visited, budget, count, announcementMade

vars == <<lamp, visited, budget, count, announcementMade>>

(* Type invariants *)
TypeOK ==
    /\ lamp \in {TRUE, FALSE}
    /\ visited \in [1..N -> {TRUE, FALSE}]
    /\ budget \in [1..N -> Nat]
    /\ count \in Nat
    /\ announcementMade \in {TRUE, FALSE}
    /\ \A i \in 1..N : budget[i] <= 1
    /\ count <= N

(* Threshold for victory *)
Threshold == IF InitialLampKnown THEN N - 1 ELSE N

(* Initial state *)
Init ==
    /\ IF InitialLampKnown THEN lamp = FALSE ELSE lamp \in {TRUE, FALSE}
    /\ visited = [i \in 1..N |-> FALSE]
    /\ budget = [i \in 1..N |-> 0]
    /\ count = 0
    /\ announcementMade = FALSE

(* Visit action for prisoner p *)
Visit(p) ==
    /\ p \in 1..N
    /\ visited' = [visited EXCEPT ![p] = TRUE]
    /\ IF p = Counter THEN
          (* counter's behavior *)
          IF lamp = TRUE THEN
              lamp' = FALSE /\ count' = count + 1
          ELSE
              lamp' = lamp /\ count' = count
          /\ budget' = budget
      ELSE
          (* non-counter prisoner *)
          IF budget[p] < 1 /\ lamp = FALSE THEN
              lamp' = TRUE /\ budget' = [budget EXCEPT ![p] = budget[p] + 1]
          ELSE
              lamp' = lamp /\ budget' = budget
          /\ count' = count
    /\ announcementMade' = announcementMade

(* Announcement action *)
Announce ==
    /\ announcementMade' = TRUE
    /\ count >= Threshold
    /\ \A i \in 1..N : visited[i] = TRUE
    /\ visited' = visited
    /\ lamp' = lamp
    /\ budget' = budget
    /\ count' = count

(* Next-state relation *)
Next == Visit(p) \/ Announce

Spec == Init /\ [][Next]_vars

Terminating == announcementMade /\ count >= Threshold

VictoryOK == <> Terminating
=============================================================================