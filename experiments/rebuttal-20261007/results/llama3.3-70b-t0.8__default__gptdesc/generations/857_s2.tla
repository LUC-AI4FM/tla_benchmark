```
MODULE PrisonerLightSwitch
EXTENDS Integers, TLC

CONSTANTS NumPrisoners, Threshold
VARIABLES light, counter, visits, announced

Init ==
  /\ light \in {0, 1}  \* 0 for off, 1 for on
  /\ counter = 0
  /\ visits = [i \in 1..NumPrisoners |-> 0]
  /\ announced = FALSE

Next ==
  \/ \E i \in 1..NumPrisoners:
    /\ light' = IF i = Threshold
              THEN 1 - light
              ELSE light
    /\ counter' = IF i = Threshold
                 THEN IF light = 1
                      THEN counter + 1
                      ELSE 0
                 ELSE counter
    /\ visits' = [visits EXCEPT ![i] = visits[i] + 1]
    /\ announced' = announced
  \/ \* announce victory
    /\ counter = IF Threshold = NumPrisoners
                THEN NumPrisoners
                ELSE 2 * NumPrisoners - 1
    /\ announced' = TRUE
    /\ UNCHANGED <<light, counter, visits>>

Spec == Init /\ [][Next]_<<light, counter, visits, announced>>
WeakFairness == <><i \in 1..NumPrisoners : Next>

THEOREM Spec => []<>announced
THEOREM Spec => announced => \A i \in 1..NumPrisoners : visits[i] > 0

FairSpec == Spec /\ WF_vars(Next, <<light, counter, visits, announced>>)

INVARIANT light \in {0, 1}
INVARIANT counter >= 0
INVARIANT \A i \in 1..NumPrisoners : visits[i] >= 0
INVARIANT announced => \A i \in 1..NumPrisoners : visits[i] > 0
```