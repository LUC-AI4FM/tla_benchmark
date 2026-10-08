```
MODULE PrisonerLightSwitch
EXTENDS Integers, TLC

CONSTANTS NumPrisoners, Threshold
VARIABLES light, counter, visits, announced

Init ==
  /\ light \in {0, 1}  \* unknown initial light state (0 for off, 1 for on)
  /\ counter = 0
  /\ visits = [i \in 1..NumPrisoners |-> 0]
  /\ announced = FALSE

Next ==
  \/ \E i \in 1..NumPrisoners :
      /\ visits[i] = 0
      /\ light' = IF light = 1 THEN 0 ELSE 1
      /\ counter' = IF i = 1 THEN (counter + 1) ELSE counter
      /\ visits' = [visits EXCEPT ![i] = 1]
      /\ announced' = announced
  \/ \E i \in 1..NumPrisoners :
      /\ visits[i] = 1
      /\ i /= 1
      /\ light' = IF light = 0 THEN 1 ELSE 0
      /\ counter' = counter
      /\ visits' = visits
      /\ announced' = announced
  \/ counter >= Threshold
      /\ announced' = TRUE
      /\ light' = light
      /\ counter' = counter
      /\ visits' = visits

Spec ==
  Init /\ [][Next]_<<light, counter, visits, announced>>
 WF_<<light, counter, visits, announced>>(Next)

THEOREM Spec => []<>announced
THEOREM Spec => announced => \A i \in 1..NumPrisoners : visits[i] = 1

Threshold == IF light = 0 THEN NumPrisoners ELSE 2 * NumPrisoners - 1
```