```
MODULE PrisonersAndSwitches
EXTENDS Integers, Sequences

CONSTANTS NumPrisoners, CounterId
VARIABLES currentPrisoner, switchA, switchB, count, visited

Init ==
  /\ currentPrisoner = 1
  /\ switchA = FALSE
  /\ switchB = FALSE
  /\ count = 0
  /\ visited = {}

Next ==
  \/ \* counter is brought into the room \*
    (currentPrisoner = CounterId
      /\ switchA
      /\ switchA' = FALSE
      /\ switchB' = ~switchB
      /\ count' = count + 1
      /\ currentPrisoner' \in 1..NumPrisoners
      /\ visited' = visited)
  \/ \* counter is brought into the room, no increment \*
    (currentPrisoner = CounterId
      /\ ~switchA
      /\ switchA' = FALSE
      /\ switchB' = ~switchB
      /\ count' = count
      /\ currentPrisoner' \in 1..NumPrisoners
      /\ visited' = visited)
  \/ \* non-counter prisoner is brought into the room, switch A up \*
    (currentPrisoner \notin {CounterId}
     /\ switchA
     /\ switchA' = FALSE
     /\ switchB' = ~switchB
     /\ count' = count
     /\ currentPrisoner' \in 1..NumPrisoners
     /\ visited' = visited \cup {currentPrisoner})
  \/ \* non-counter prisoner is brought into the room, switch A down and two moves left \*
    (currentPrisoner \notin {CounterId}
     /\ ~switchA
     /\ switchB
     /\ switchA' = TRUE
     /\ switchB' = FALSE
     /\ count' = count
     /\ currentPrisoner' \in 1..NumPrisoners
     /\ visited' = visited \cup {currentPrisoner})
  \/ \* non-counter prisoner is brought into the room, switch A down and one move left \*
    (currentPrisoner \notin {CounterId}
     /\ ~switchA
     /\ ~switchB
     /\ switchA' = TRUE
     /\ switchB' = FALSE
     /\ count' = count
     /\ currentPrisoner' \in 1..NumPrisoners
     /\ visited' = visited)

Spec ==
  /\ Init
  /\ [][Next]_<<currentPrisoner, switchA, switchB, count, visited>>
  /\ WF_vars(<< >>)(currentPrisoner = CounterId)
  /\ \* fairness for each non-counter prisoner \*
    (WF_vars(<< >>)(currentPrisoner \notin {CounterId}))
  /\ \* safety property: when protocol declares completion, every prisoner has visited the room \*
    []((count = NumPrisoners - 1) => (visited = 1..NumPrisoners))
  /\ \* liveness property: declaration condition is eventually reached \*
    <>(count = NumPrisoners - 1)

THEOREM Spec => []((count = NumPrisoners - 1) => (visited = 1..NumPrisoners))
THEOREM Spec => <>(count = NumPrisoners - 1)
```