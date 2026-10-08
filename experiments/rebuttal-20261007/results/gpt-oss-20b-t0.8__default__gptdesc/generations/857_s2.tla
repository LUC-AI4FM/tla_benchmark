MODULE PrisonerLightPuzzle
EXTENDS Naturals

CONSTANTS N, COUNTER, Variant \* Variant ∈ {"known","unknown"}

(* ------------------------------------------------------------------ *)
\* State Variables
VARIABLE light, Signaled, Count, Visited, VictoryAnnounced

vars == <<light, Signaled, Count, Visited, VictoryAnnounced>>

(* ------------------------------------------------------------------ *)
\* Constants
PRM == 1 .. N

maxSignal(p) ==
  IF Variant = "known" THEN 1 ELSE 2

threshold ==
  IF Variant = "known" THEN N ELSE (2*N - 1)

(* ------------------------------------------------------------------ *)
\* Initial state
Init ==
  /\ light ∈ {"off","on"}  
     /\ IF Variant = "known" THEN light = "off" ELSE TRUE
  /\ Signaled = [p \in PRM |-> 0]
  /\ Count = 0
  /\ Visited = {}
  /\ VictoryAnnounced = FALSE

(* ------------------------------------------------------------------ *)
\* Non‑counter prisoner action
ActionNonCounter(p) ==
  LET
    SIGNAL == (light = "off") /\ Signaled[p] < maxSignal(p)
  IN
  /\ p ∈ PRM \ {COUNTER}
  /\ Visited'   = Visited ∪ {p}
  /\ Signaled'  = [Signaled EXCEPT ![p] = Signaled[p] + IF SIGNAL THEN 1 ELSE 0]
  /\ light'     = IF SIGNAL THEN "on" ELSE light
  /\ Count'     = Count
  /\ VictoryAnnounced' = VictoryAnnounced

(* ------------------------------------------------------------------ *)
\* Counter prisoner action
ActionCounter ==
  LET
    NEW_COUNT   == IF light = "on" THEN Count + 1 ELSE Count
    NEW_LIGHT   == IF light = "on" THEN "off" ELSE light
    NEW_VISITED == Visited ∪ {COUNTER}
    ANNOUNCE    == IF NEW_COUNT >= threshold /\ NEW_VISITED = PRM THEN TRUE ELSE VictoryAnnounced
  IN
  /\ COUNTER ∈ PRM
  /\ Visited'          = NEW_VISITED
  /\ Count'            = NEW_COUNT
  /\ light'            = NEW_LIGHT
  /\ VictoryAnnounced' = ANNOUNCE

(* ------------------------------------------------------------------ *)
\* Prisoner action chosen by the warden
prisonerAction(p) ==
  IF p = COUNTER THEN ActionCounter ELSE ActionNonCounter(p)

Next ==
  ∃ p ∈ PRM : prisonerAction(p)

Spec == Init /\ [][Next]_vars /\ WF_action(Next)

(* ------------------------------------------------------------------ *)
\* Invariant: any victory announcement implies all prisoners have visited
Inv == VictoryAnnounced => (Visited = PRM)

(* ------------------------------------------------------------------ *)
\* Liveness property: eventually a victory is announced
Liveness == []<>(VictoryAnnounced)
===============================================================================