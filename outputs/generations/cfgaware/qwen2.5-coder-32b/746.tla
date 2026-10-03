------------------------------- MODULE Chameneos -------------------------------

CONSTANTS
    N \* Global limit on meetings
    Colors \* Set of possible colors

VARIABLES
    color \* Mapping from chameneos to their current color
    met \* Mapping from chameneos to their meeting count
    meetingPlace \* The shared meeting place slot, either << >> or a pair of chameneos
    totalMeetings \* Total number of meetings that have occurred

ASSUME N > 0
ASSUME Cardinality(Colors) >= 2

TypeOK == 
    /\ color \in [Chameneos -> Colors]
    /\ met \in [Chameneos -> Nat]
    /\ meetingPlace \in {<< >>} \cup {[c1, c2] \in Chameneos \X Chameneos : c1 # c2}
    /\ totalMeetings \in 0..N

ComplementColor(c1, c2) == 
    CHOOSE c \in Colors : c # c1 /\ c # c2

Init ==
    /\ color = [c \in Chameneos |-> CHOOSE col \in Colors]
    /\ met = [c \in Chameneos |-> 0]
    /\ meetingPlace = << >>
    /\ totalMeetings = 0

TryToMeet(c) ==
    /\ meetingPlace = << >>
    /\ totalMeetings < N
    /\ meetingPlace' = <<c, CHOOSE d \in Chameneos : d # c>>
    /\ UNCHANGED <<color, met, totalMeetings>>

Fade(c) ==
    /\ totalMeetings >= N
    /\ UNCHANGED <<meetingPlace, color, met, totalMeetings>>

Meet ==
    LET <<c1, c2>> == meetingPlace
        newColor == ComplementColor(color[c1], color[c2])
    IN
        /\ meetingPlace = <<c1, c2>>
        /\ totalMeetings < N
        /\ meetingPlace' = << >>
        /\ color' = [color EXCEPT ![c1] = newColor, ![c2] = newColor]
        /\ met' = [met EXCEPT ![c1] = met[c1] + 1, ![c2] = met[c2] + 1]
        /\ totalMeetings' = totalMeetings + 1

Next ==
    \/ \E c \in Chameneos : TryToMeet(c)
    \/ \E c \in Chameneos : Fade(c)
    \/ Meet

SumMet == 
    LET sum == \SUM c \in Chameneos : met[c]
    IN
        totalMeetings = N => sum = 2 * N

Spec ==
    Init /\ [][Next]_<<color, met, meetingPlace, totalMeetings>>

=============================================================================