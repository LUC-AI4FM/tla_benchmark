```
MODULE PrisonersAndSwitches
EXTENDS Integers, FiniteSets

CONSTANTS NumPrisoners
VARIABLES counter, switchA, switchB, count, visited

Init ==
  /\ counter = 1
  /\ switchA = "down"
  /\ switchB = "down"
  /\ count = 0
  /\ visited = {}

Next ==
  \/ \E p \in (1..NumPrisoners) :
      IF p = counter
      THEN
        IF switchA = "up"
        THEN
          /\ switchA' = "down"
          /\ count' = count + 1
          /\ switchB' = switchB
          /\ visited' = visited
        ELSE
          /\ switchA' = switchA
          /\ count' = count
          /\ switchB' = switchB
          /\ visited' = visited \cup {p}
      ELSE
        IF switchA = "down"
        THEN
          /\ switchA' \in {"up", "down"}
          /\ count' = count
          /\ switchB' = IF switchB = "up" THEN "down" ELSE "up"
          /\ visited' = visited \cup {p}
        ELSE
          /\ switchA' = switchA
          /\ count' = count
          /\ switchB' = switchB
          /\ visited' = visited \cup {p}

Spec ==
  /\ Init
  /\ [][Next]_<<counter, switchA, switchB, count, visited>>
  /\ WF_vars(<<1..NumPrisoners>> \ {counter})
  /\ SF_vars(counter)

SafetyInv ==
  visited \subseteq (1..NumPrisoners)

LivenessProp ==
  <>((count = 2 * (NumPrisoners - 1)) /\
      (visited = (1..NumPrisoners)))

THEOREM Spec => []SafetyInv
THEOREM Spec => LivenessProp
```
Note: In TLA+, `[]` denotes "always" and `<>` denotes "eventually". The `_` symbol in `[Next]_<<vars>>` is used to specify the variables that are changed by the `Next` action. `WF_vars` and `SF_vars` denote weak fairness and strong fairness, respectively.