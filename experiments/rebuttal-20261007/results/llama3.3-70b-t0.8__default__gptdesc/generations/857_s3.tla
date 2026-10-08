```
MODULE PrisonerLightSwitch
EXTENDS Integers, TLC

CONSTANTS NumPrisoners, InitialLightState
VARIABLES light, counter, visits, announced

Init ==
  /\ light = IF InitialLightState = "unknown" THEN FALSE ELSE FALSE
  /\ counter = 0
  /\ visits = [i \in 1..NumPrisoners |-> 0]
  /\ announced = FALSE

Next ==
  \/ \E i \in 1..NumPrisoners:
      /\ light' = IF i = counter THEN ¬light ELSE light
      /\ counter' = IF i = counter THEN counter + 1 ELSE counter
      /\ visits' = [visits EXCEPT ![i] = visits[i] + 1]
      /\ announced' = announced
  \/ \E i \in 1..NumPrisoners:
      /\ i /= counter
      /\ light' = TRUE
      /\ counter' = counter
      /\ visits' = visits
      /\ announced' = announced
  \/ (counter >= IF InitialLightState = "unknown" THEN 2 * NumPrisoners - 1 ELSE NumPrisoners)
      /\ announced' = TRUE
      /\ light' = light
      /\ counter' = counter
      /\ visits' = visits

Spec ==
  Init /\ [][Next]_<<light, counter, visits, announced>>
  WF_(WardenSelect)(Next)

THEOREM Spec => []<>announced
INVARIANT AnnounceImpliesVisited == announced => \A i \in 1..NumPrisoners: visits[i] >= 1

Fairness ==
  WF_(WardenSelect)(\E i \in 1..NumPrisoners: Next)

WardenSelect == \E i \in 1..NumPrisoners: Next
```