```
MODULE PrisonersAndSwitches
EXTENDS Integers, TLC

CONSTANTS NumPrisoners
VARIABLES counter, switchA, switchB, count, visits

Init ==
  /\ counter = 1
  /\ switchA = "down"
  /\ switchB = "down"
  /\ count = 0
  /\ visits = << >>

Next ==
  \/ \E p \in (1..NumPrisoners) :
    /\ IF p = counter
      THEN
        /\ IF switchA = "up"
          THEN
            /\ switchA' = "down"
            /\ count' = count + 1
            /\ visits' = visits
            /\ switchB' = switchB
          ELSE
            /\ switchA' = switchA
            /\ count' = count
            /\ visits' = visits
            /\ switchB' = IF switchB = "up" THEN "down" ELSE "up"
        ELSE
          /\ IF switchA = "up"
            THEN
              /\ switchA' = switchA
              /\ count' = count
              /\ visits' = visits
              /\ switchB' = switchB
            ELSE
              /\ switchA' = "up"
              /\ count' = count
              /\ visits' = visits \cup {p}
              /\ switchB' = IF switchB = "up" THEN "down" ELSE "up"
      /\ UNCHANGED <<switchA, switchB, count, visits>>

Spec ==
  Init /\ [][Next]_<<counter, switchA, switchB, count, visits>>
  /\ WF_vars(Next, <<1..NumPrisoners>>)
  /\ SF_vars(Next, <<1..NumPrisoners>>)

SafetyProperty ==
  []((\A p \in (1..NumPrisoners) : p \in visits) => (count = NumPrisoners - 1))

LivenessProperty ==
  <>(\A p \in (1..NumPrisoners) : p \in visits)
```
Note: The above TLA+ code assumes the existence of `TLC` module, which is part of the standard TLA+ distribution and provides definitions for common data structures like sequences. Also note that this model uses weak fairness to guarantee that every prisoner will be selected infinitely often, as required by the problem description.