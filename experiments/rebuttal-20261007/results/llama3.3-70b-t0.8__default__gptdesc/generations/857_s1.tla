```
MODULE PrisonerPuzzle
EXTENDS Integers, TLC

CONSTANTS NumPrisoners, CounterPrisoner
VARIABLES lamp, visits, counter, selected, victory

Init ==
  /\ lamp \in {True, False}
  /\ visits = [i \in 1..NumPrisoners |-> 0]
  /\ counter = 0
  /\ selected = NULL
  /\ victory = FALSE

Next ==
  /\ (selected = NULL)
    /\ (selected' \in 1..NumPrisoners)
    /\ (visits' = [visits EXCEPT ![selected'] = @ + 1])
    /\ IF selected' = CounterPrisoner
      THEN
        /\ IF counter < (2 * NumPrisoners - 1)
          THEN
            /\ lamp' = IF lamp THEN True ELSE False
            /\ counter' = counter + 1
          ELSE
            /\ victory' = TRUE
        ELSE
          /\ lamp' = \neg lamp
          /\ counter' = counter
      ELSE
        /\ lamp' = \neg lamp
        /\ counter' = counter
    /\ UNCHANGED <<visits, selected, victory>>

Spec ==
  /\ Init
  /\ [][Next]_<<lamp, visits, counter, selected, victory>>
  /\ WF_vars(<<selected>>)

SafetyInv ==
  /\ victory => \A i \in 1..NumPrisoners : visits[i] > 0

LivenessProp ==
  <>victory

THEOREM Spec => []SafetyInv
THEOREM Spec => LivenessProp
```