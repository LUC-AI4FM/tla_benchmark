```
MODULE PrisonerLampPuzzle
EXTENDS Integers, FiniteSets

CONSTANTS N, config
VARIABLES lamp, count, visited, wardenSelections, lastVisit

Init ==
  /\ lamp = IF config = "known" THEN FALSE ELSE Choose({TRUE, FALSE})
  /\ count = 0
  /\ visited = {}
  /\ wardenSelections = <<>>
  /\ lastVisit = <<>>

Next ==
  /\ \/ \E p \in (1..N) :
        /\ wardenSelections' = Append(wardenSelections, p)
        /\ IF config = "known" THEN
            IF p = 1 /\ lamp = TRUE
              THEN
                /\ lamp' = FALSE
                /\ count' = count + 1
                /\ visited' = visited \cup {p}
              ELSE
                /\ lamp' = IF p /= 1 THEN TRUE ELSE lamp
                /\ count' = count
                /\ visited' = IF p /= 1 /\ lamp = FALSE THEN visited \cup {p} ELSE visited
            ELSE
              IF p = 1 /\ (lamp = TRUE \/ count < 2*N - 1)
                THEN
                  /\ lamp' = FALSE
                  /\ count' = count + 1
                  /\ visited' = visited \cup {p}
                ELSE
                  /\ lamp' = IF p /= 1 /\ (lamp = FALSE /\ Count({q \in (1..N) : q /= p}) < 2) THEN TRUE ELSE lamp
                  /\ count' = IF p /= 1 /\ lamp = FALSE /\ Count({q \in (1..N) : q /= p}) < 2 THEN count + 1 ELSE count
                  /\ visited' = IF p /= 1 /\ lamp = FALSE /\ Count({q \in (1..N) : q /= p}) < 2 THEN visited \cup {p} ELSE visited
        /\ lastVisit' = Append(lastVisit, p)
      \/ \E p \in (1..N) :
          /\ wardenSelections' = wardenSelections
          /\ lamp' = lamp
          /\ count' = count
          /\ visited' = visited
          /\ lastVisit' = lastVisit

Spec ==
  /\ Init
  /\ [][Next]_<<lamp, count, visited, wardenSelections, lastVisit>>
  /\ WF_(wardenSelections, (1..N))
  /\ SF_(wardenSelections, (1..N))

THEOREM Spec => []~<(visited = (1..N))>

THEOREM Spec => <>(count = IF config = "known" THEN N ELSE 2*N - 1)

INVARIANT count <= IF config = "known" THEN N ELSE 2*N - 1
```