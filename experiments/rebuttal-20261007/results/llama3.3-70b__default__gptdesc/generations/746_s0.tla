```
MODULE Chameneos
EXTENDS Integers, FiniteSets

CONSTANTS Colors, N
VARIABLES meetingPlace, meetingCounters, totalMeetings

Init ==
  /\ meetingPlace = <<>>
  /\ meetingCounters \in [Chameneos -> 0..N]
  /\ totalMeetings = 0

Next ==
  /\ (meetingPlace = <<>>)
    => (meetingPlace' = <<c \in Chameneos : c /= meetingPlace >>)
      /\ (meetingCounters' = [meetingCounters EXCEPT ![c] = meetingCounters[c] + 1])
      /\ (totalMeetings' = totalMeetings + 1)
  /\ (meetingPlace /= <<>>)
    => (meetingPlace' = <<>>)
      /\ (meetingCounters' = meetingCounters)
      /\ (totalMeetings' = totalMeetings)

Spec ==
  Init /\ [][Next]_vars

THEOREM Spec => []((totalMeetings = N) => (+ meetingCounters = 2 * N))
```