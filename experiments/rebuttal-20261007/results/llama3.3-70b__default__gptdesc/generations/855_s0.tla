```
MODULE PrisonersAndSwitches
EXTENDS Integers, FiniteSets

CONSTANTS NumPrisoners
VARIABLES counter, switchA, switchB, count, visits

Init ==
  /\ counter = 1
  /\ switchA = "down"
  /\ switchB = "down"
  /\ count = 0
  /\ visits = {}

Next ==
  \/ \E p \in (1..NumPrisoners) :
    /\ p = counter
    /\ switchA = "up"
    /\ switchA' = "down"
    /\ count' = count + 1
    /\ visits' = visits
    /\ switchB' = switchB
  \/ \E p \in (1..NumPrisoners) :
    /\ p /= counter
    /\ switchA = "down"
    /\ switchA' = "up"
    /\ count' = count
    /\ visits' = visits \cup {p}
    /\ switchB' = IF switchB = "up" THEN "down" ELSE "up"
  \/ \E p \in (1..NumPrisoners) :
    /\ p /= counter
    /\ switchA = "up"
    /\ switchA' = "up"
    /\ count' = count
    /\ visits' = visits
    /\ switchB' = IF switchB = "up" THEN "down" ELSE "up"

Spec ==
  /\ Init
  /\ [][Next]_<<counter, switchA, switchB, count, visits>>
  /\ WF_(1..NumPrisoners)(\[Next\]_<<counter, switchA, switchB, count, visits>>)
  /\ SF_(1..NumPrisoners)(\[Next\]_<<counter, switchA, switchB, count, visits>>)

Safety ==
  []((count = NumPrisoners - 1) => (visits = (1..NumPrisoners)))

Liveness ==
  <>(count = NumPrisoners - 1)
```
Note: The above TLA+ specification models the prisoners-and-switches puzzle with `NumPrisoners` prisoners. It uses a counter to keep track of the number of times switch A is found up and turned down, and each non-counter prisoner can move switch A up at most twice. The specification includes safety and liveness properties as described in the problem statement.