```
MODULE PrisonerLightSwitch
EXTENDS Integers, TLC

CONSTANTS NumPrisoners, Threshold
VARIABLES lamp, counter, visits, announced

Init ==
  /\ lamp \in {0, 1}  (* unknown initial light state *)
  /\ counter = 0
  /\ visits = [i \in 1..NumPrisoners |-> 0]
  /\ announced = FALSE

Next ==
  \/ \E i \in 1..NumPrisoners :
      /\ lamp' = IF i = Threshold THEN 1 ELSE lamp
      /\ counter' = IF i = Threshold THEN counter + 1 ELSE counter
      /\ visits' = [visits EXCEPT ![i] = visits[i] + 1]
      /\ announced' = announced
  \/ \E i \in 1..NumPrisoners :
      /\ i # Threshold
      /\ lamp' = 1 - lamp  (* toggle light *)
      /\ counter' = counter
      /\ visits' = [visits EXCEPT ![i] = visits[i] + 1]
      /\ announced' = announced
  \/ announced' = TRUE
  /\ lamp' = lamp
  /\ counter' = counter
  /\ visits' = visits

Spec ==
  Init /\ [][Next]_<<lamp, counter, visits, announced>>
  WF_Vars(<<1..NumPrisoners>>)

Theorem ==
  Spec => []<>(announced = TRUE)

SafetyProperty ==
  announced => \A i \in 1..NumPrisoners : visits[i] > 0

THEOREM Theorem
THEOREM Spec => []SafetyProperty
```