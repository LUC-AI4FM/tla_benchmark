```
MODULE Chameneos
EXTENDS Integers, FiniteSets

CONSTANTS Colors, N
VARIABLES meetingPlace, meetingCounters, totalMeetings

Init ==
  /\ meetingPlace = None
  /\ meetingCounters \in [Chameneos -> 0]
  /\ totalMeetings = 0

Next ==
  (\E c \in Chameneos :
    /\ meetingPlace = None
    /\ meetingPlace' = c
    /\ meetingCounters' = [meetingCounters EXCEPT ![c] = meetingCounters[c] + 1]
    /\ totalMeetings' = totalMeetings + 1
  ) \lor
  (\E c1, c2 \in Chameneos :
    /\ meetingPlace = c1
    /\ c2 /= c1
    /\ meetingPlace' = None
    /\ meetingCounters' = [meetingCounters EXCEPT ![c1] = meetingCounters[c1], ![c2] = meetingCounters[c2] + 1]
    /\ totalMeetings' = totalMeetings + 1
  ) \lor
  (\E c \in Chameneos :
    /\ meetingPlace = None
    /\ meetingPlace' = None
    /\ meetingCounters' = meetingCounters
    /\ totalMeetings' = IF totalMeetings < N THEN totalMeetings ELSE totalMeetings
  )

Spec == Init /\ [][Next]_vars

THEOREM Spec => []((totalMeetings = N) => (\* c \in Chameneos : meetingCounters[c]) = 2 * N)
```