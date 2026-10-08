------------------------------- MODULE Chameneos -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumChameneos, Colors, N

VARIABLES color, meetings, totalMeetings, meetingPlace

Init == /\ color \in [1..NumChameneos -> Colors]
        /\ meetings \in [1..NumChameneos -> 0]
        /\ totalMeetings = 0
        /\ meetingPlace = <<>>

Next ==
    LET newColor[c1, c2] == CHOOSE c \in Colors : c /= c1 /\ c /= c2
        meetChameneo == CHOOSE i \in 1..NumChameneos : meetingPlace = <<>> \/ meetingPlace[1] # i
        otherChameneo == meetingPlace[1]
    IN
    \/ /\ meetingPlace = <<>>
       /\ meetChameneo \in 1..NumChameneos
       /\ meetingPlace' = <<meetChameneo>>
       /\ UNCHANGED <<color, meetings, totalMeetings>>
    \/ /\ meetingPlace /= <<>>
       /\ otherChameneo \in 1..NumChameneos
       /\ meetChameneo \in 1..NumChameneos
       /\ meetChameneo # otherChameneo
       /\ color' = [color EXCEPT ![meetChameneo] = newColor[color[meetChameneo], color[otherChameneo]],
                             ![otherChameneo] = newColor[color[otherChameneo], color[meetChameneo]]]
       /\ meetings' = [meetings EXCEPT ![meetChameneo] = meetings[meetChameneo] + 1,
                                ![otherChameneo] = meetings[otherChameneo] + 1]
       /\ totalMeetings' = totalMeetings + 1
       /\ meetingPlace' = <<>>
    \/ /\ totalMeetings >= N
       /\ UNCHANGED <<color, meetings, meetingPlace>>

Spec == Init /\ [][Next]_<<color, meetings, totalMeetings, meetingPlace>>

ArithmeticProperty ==
    /\ totalMeetings < N
    \/ totalMeetings >= N /\ \A i \in 1..NumChameneos : \Sum j \in 1..i : meetings[j] = 2 * totalMeetings

=============================================================================