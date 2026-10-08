```
MODULE Chameneos
EXTENDS Integers, TLC

CONSTANTS N, Colors
VARIABLES meetSlot, meetingCounters, totalMeetings

Init ==
  /\ meetSlot = << >> 
  /\ meetingCounters = [i \in 1..Cardinality(Colors) |-> 0]
  /\ totalMeetings = 0

Next ==
  /\ IF totalMeetings < N
    THEN
      /\ meetSlot' = IF meetSlot = << >> 
                  THEN <<CHOOSE c1, c2 \in Colors : c1 /= c2>>
                  ELSE meetSlot
      /\ meetingCounters' = [meetingCounters EXCEPT ![c1] = @ + 1, ![c2] = @ + 1]
        WHERE <<c1, c2>> = meetSlot'
      /\ totalMeetings' = totalMeetings + 1
    ELSE
      /\ meetSlot' = meetSlot
      /\ meetingCounters' = meetingCounters
      /\ totalMeetings' = totalMeetings

Spec == Init /\ [][Next]_meetSlot, meetingCounters, totalMeetings

THEOREM Spec => []((totalMeetings = N) => (+ meetingCounters = 2 * N))
```