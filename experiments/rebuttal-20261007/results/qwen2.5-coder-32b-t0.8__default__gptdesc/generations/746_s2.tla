------------------------------- MODULE Chameneos ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS NumChameneoses, Colors, N

VARIABLES color, meetingCount, place, totalMeetings

Init == /\ color \in [1..NumChameneoses -> Colors]
        /\ meetingCount \in [1..NumChameneoses -> 0]
        /\ place = << >>
        /\ totalMeetings = 0

Next == \/ \E i \in 1..NumChameneoses : 
               /\ color[i] \in Colors
               /\ meetingCount[i] < N
               /\ place = << >> 
               /\ \/ /\ color[i]' = color[i]
                  /\ meetingCount' = [meetingCount EXCEPT ![i] = meetingCount[i]]
                  /\ totalMeetings' = totalMeetings
                  /\ place' = << i, color[i] >>
              [] /\ \E j \in 1..NumChameneoses :
                     /\ i # j
                     /\ place = << j, color[j] >> 
                     /\ color[i]' \in Colors
                     /\ meetingCount'[i] = meetingCount[i] + 1
                     /\ meetingCount'[j] = meetingCount[j] + 1
                     /\ totalMeetings' = totalMeetings + 1
                     /\ place' = << >>
        [] \/ \E i \in 1..NumChameneoses : 
               /\ color[i] \in Colors
               /\ meetingCount[i] >= N
               /\ place = << >> 
               /\ color'[i] = color[i]
               /\ meetingCount'[i] = meetingCount[i]
               /\ totalMeetings' = totalMeetings
               /\ place' = place

Spec == Init /\ [][Next]_<<color, meetingCount, place, totalMeetings>>

SumMeetingCountEquals2N == totalMeetings >= N => \A i \in 1..NumChameneoses : \E sum \in Nat : \A j \in 1..NumChameneoses : Sum({meetingCount[j] : j \in 1..NumChameneoses}) = 2 * totalMeetings

================================================================================