```
MODULE PrisonerPuzzle
EXTENDS Integers, FiniteSets

CONSTANTS NumPrisoners, CounterId
VARIABLES switch1, switch2, visited, count, declared

Init ==
  /\ switch1 \in {0, 1}
  /\ switch2 \in {0, 1}
  /\ visited = {}
  /\ count = 0
  /\ declared = FALSE

Next ==
  /\ IF declared THEN UNCHANGED <<switch1, switch2, visited, count, declared>>
  /\ ELSE 
    /\ \E p \in 1..NumPrisoners :
      /\ (p = CounterId) =>
        /\ (switch1' = 1 - switch1) /\ (switch2' = switch2)
        /\ IF p \notin visited THEN
          /\ count' = count + 1
          /\ visited' = visited \cup {p}
          ELSE
          /\ count' = count
          /\ visited' = visited
        /\ declared' = (count' = NumPrisoners - 1)
      /\ (p \neq CounterId) =>
        /\ (switch2' = 1 - switch2) /\ (switch1' = switch1)
        /\ IF p \notin visited THEN
          /\ count' = count
          /\ visited' = visited \cup {p}
        ELSE
          /\ count' = count
          /\ visited' = visited
        /\ declared' = declared
      /\ (p \notin 1..NumPrisoners) => UNCHANGED <<switch1, switch2, visited, count, declared>>
  /\ IF declared THEN count = NumPrisoners - 1 ELSE TRUE

Spec ==
  /\ Init
  /\ [][Next]_<<switch1, switch2, visited, count, declared>>
  /\ WF_(p \in 1..NumPrisoners)(\E p' \in 1..NumPrisoners : Next)
  /\ SF_(p \in 1..NumPrisoners)(\E p' \in 1..NumPrisoners : Next)

THEOREM Spec => []((declared) => (visited = 1..NumPrisoners \ {CounterId}))
THEOREM Spec => <>declared
```