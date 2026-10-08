----------------------------- MODULE Chameneos -----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS
    N \* Global limit of meetings
    Colors \* Set of possible colors

VARIABLES
    color \* Color of each chameneo indexed by its identifier
    meetingCount \* Meeting count of each chameneo indexed by its identifier
    totalMeetings \* Total number of meetings that have occurred
    meetingPlace \* Slot for a chameneo to meet another

Init ==
    /\ meetingPlace = <<>>
    /\ totalMeetings = 0
    /\ color \in [DOMAIN color -> Colors]
    /\ meetingCount \in [DOMAIN meetingCount -> 0]

Complement(c1, c2) == IF c1 = c2 THEN c1 ELSE (Colors - {c1, c2})[1]

Next ==
    \/ \E i \in DOMAIN color : 
        \/ meetingPlace = <<>>
            /\ meetingCount' = [meetingCount EXCEPT ![i] = meetingCount[i]]
            /\ color' = [color EXCEPT ![i] = color[i]]
            /\ totalMeetings' = totalMeetings
            /\ meetingPlace' = <<i, color[i]>>
        \/ \E j \in DOMAIN color : i # j /\ meetingPlace = <<j, color[j]>>
            /\ meetingCount' = [meetingCount EXCEPT ![i] = meetingCount[i] + 1, ![j] = meetingCount[j] + 1]
            /\ color' = [color EXCEPT ![i] = Complement(color[i], color[j]), ![j] = Complement(color[j], color[i])]
            /\ totalMeetings' = totalMeetings + 1
            /\ meetingPlace' = <<>>
    \/ meetingPlace # <<>> /\ totalMeetings >= N
        /\ meetingCount' = meetingCount
        /\ color' = color
        /\ totalMeetings' = totalMeetings
        /\ meetingPlace' = meetingPlace

MeetingInvariant ==
    \A i \in DOMAIN meetingCount : meetingCount[i] >= 0

TotalMeetingsInvariant ==
    totalMeetings >= 0 /\ totalMeetings <= N

SumOfMeetingCounts ==
    Sum({meetingCount[i]: i \in DOMAIN meetingCount}) = 2 * totalMeetings

Spec ==
    Init /\ [][Next]_<<color, meetingCount, totalMeetings, meetingPlace>>

=============================================================================