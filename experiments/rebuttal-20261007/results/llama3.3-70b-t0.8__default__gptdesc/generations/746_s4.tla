```
MODULE Chameneos
EXTENDS Integers, TLC
CONSTANTS N, Colors
VARIABLES meetingPlace, meetingCounters, totalMeetings

Init ==
  /\ meetingPlace = NULL
  /\ meetingCounters \in [1..Cardinality(Colors) -> 0]
  /\ totalMeetings = 0

Next ==
  \/ \E c \in Colors :
      /\ meetingPlace = NULL
      /\ meetingPlace' = c
      /\ meetingCounters' = [meetingCounters EXCEPT ![c] = meetingCounters[c] + 1]
      /\ totalMeetings' = totalMeetings + 1
      /\ IF totalMeetings' = N THEN meetingPlace' = Fade ELSE TRUE
  \/ \E c \in Colors :
      /\ meetingPlace \in Colors
      /\ meetingPlace /= c
      /\ meetingPlace' = NULL
      /\ meetingCounters' = [meetingCounters EXCEPT ![meetingPlace] = meetingCounters[meetingPlace] + 1, ![c] = meetingCounters[c] + 1]
      /\ totalMeetings' = totalMeetings + 1
      /\ IF totalMeetings' = N THEN meetingPlace' = Fade ELSE TRUE

Spec == Init /\ [][Next]_vars

THEOREM Spec => []((totalMeetings = N) => (+ meetingCounters = 2 * N))
```