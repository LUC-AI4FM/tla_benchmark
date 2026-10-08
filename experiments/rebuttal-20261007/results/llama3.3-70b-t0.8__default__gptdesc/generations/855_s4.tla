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
    /\ p = counter
    /\ switchA = "up"
    /\ switchA' = "down"
    /\ count' = count + 1
    /\ switchB' = switchB
    /\ visited' = visited
  \/ \E p \in (1..NumPrisoners) :
    /\ p /= counter
    /\ switchA = "down"
    /\ switchA' = "up"
    /\ count' = count
    /\ switchB' = IF switchB = "up" THEN "down" ELSE "up"
    /\ visited' = visited \cup {p}
  \/ \E p \in (1..NumPrisoners) :
    /\ p /= counter
    /\ switchA = "up"
    /\ switchA' = "up"
    /\ count' = count
    /\ switchB' = IF switchB = "up" THEN "down" ELSE "up"
    /\ visited' = visited \cup {p}

Spec ==
  Init /\ [][Next]_<<counter, switchA, switchB, count, visited>>
  /\ WF_(1..NumPrisoners)(\[Next\]_<<counter, switchA, switchB, count, visited>>)
  /\ [](visited = (1..NumPrisoners)) => [](count >= 2 * (NumPrisoners - 1))
  /\ <>(count >= 2 * (NumPrisoners - 1))

THEOREM Spec => []<>(count >= 2 * (NumPrisoners - 1))
```