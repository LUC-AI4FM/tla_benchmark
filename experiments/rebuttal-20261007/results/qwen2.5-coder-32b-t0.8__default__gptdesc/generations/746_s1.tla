---------------------------- MODULE Chameneos ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS NumChameneoses, Colors, N

VARIABLES colors, meetings, totalMeetings

Init == 
  /\ colors \in [1..NumChameneoses -> Colors]
  /\ meetings \in [1..NumChameneoses -> 0]
  /\ totalMeetings = 0
  /\ (totalMeetings < N)

Next ==
  LET meetingPlace \in SUBSET {1..NumChameneoses} : card(meetingPlace) = 2
      AND /\ \/ /\ \E i, j \in meetingPlace: colors[i] <> colors[j]
                 \/ totalMeetings >= N
          /\ \/ /\ \A i \in meetingPlace: meetings'[i] = meetings[i] + 1
                 \/ totalMeetings' = totalMeetings
          /\ colors' = [colors EXCEPT ![meetingPlace[1]] = colors[meetingPlace[2]], ![meetingPlace[2]] = colors[meetingPlace[1]]]
          /\ meetings' \in [meetings EXCEPT ![meetingPlace[1]] = meetings[meetingPlace[1]] + 1, ![meetingPlace[2]] = meetings[meetingPlace[2]] + 1]
          /\ totalMeetings' = IF card(meetingPlace) > 0 THEN totalMeetings + 1 ELSE totalMeetings
  IN \/ \E meetingPlace : meetingPlace \in SUBSET {1..NumChameneoses} : card(meetingPlace) = 2 /\ \/ colors'[meetingPlace[1]] = colors[meetingPlace[2]]
                                                                                           \/ colors'[meetingPlace[2]] = colors[meetingPlace[1]]
                                                                                           \/ meetings' \in [meetings EXCEPT ![meetingPlace[1]] = meetings[meetingPlace[1]] + 1, ![meetingPlace[2]] = meetings[meetingPlace[2]] + 1]
                                                                                           \/ totalMeetings' = IF card(meetingPlace) > 0 THEN totalMeetings + 1 ELSE totalMeetings
     \/ /\ colors' = colors
        /\ meetings' = meetings
        /\ totalMeetings' = totalMeetings

Spec ==
  Init /\ [][Next]_<<colors, meetings, totalMeetings>>

MeetingInvariant ==
  \A i \in 1..NumChameneoses: meetings[i] >= 0

TotalMeetingsInvariant ==
  totalMeetings <= N

ArithmeticProperty ==
  [](totalMeetings = N) => (\A i \in 1..NumChameneoses: Sum({meetings[i] : i \in 1..NumChameneoses}) = 2 * N)

==================================================