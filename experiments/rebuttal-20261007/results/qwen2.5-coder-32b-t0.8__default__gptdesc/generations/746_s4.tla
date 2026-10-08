------------------------------ MODULE Chameneos ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    NumChameneoses,
    Colors,
    N

VARIABLES 
    color,       \* color[c] is the current color of chameneose c
    meetings,    \* meetings[c] is the number of meetings chameneose c has had
    meetingPlace,\* meetingPlace is the slot where a pair of chameneoses meet or < >
    totalMeetings\* totalMeetings is the total number of meetings that have occurred

Init == 
    /\ color \in [1..NumChameneoses -> Colors]
    /\ meetings \in [1..NumChameneoses -> {0}]
    /\ meetingPlace = <>
    /\ totalMeetings = 0

ChangeColor(c1, c2) ==
    LET complementColor == CHOOSE c \in Colors : c /= c1 /\ c /= c2
    IN  complementColor

Next == 
    \/ \/ \E c \in 1..NumChameneoses : meetingPlace = <> /\ color[c] \in Colors
            /\ /\ meetingPlace' = <<c, color[c]>>
               /\ UNCHANGED <<color - {c}, meetings, totalMeetings>>
       \/ \E <<c1, col>> \in SUBSET meetingPlace : 
                \E c2 \in 1..NumChameneoses :
                    /\ c2 /= fst(col)
                    /\ color[c2] = snd(col)
                    /\ \/ totalMeetings < N
                        /\ /\ meetingPlace' = <>
                           /\ color'[c1] = ChangeColor(color[c1], color[c2])
                           /\ color'[c2] = ChangeColor(color[c1], color[c2])
                           /\ meetings'[c1] = meetings[c1] + 1
                           /\ meetings'[c2] = meetings[c2] + 1
                           /\ totalMeetings' = totalMeetings + 1
                        \/ totalMeetings >= N
                        /\ /\ meetingPlace' = <<c2, color[c2]>>
                           /\ UNCHANGED <<color - {c2}, meetings, totalMeetings>>
       \/ \E <<c, col>> \in SUBSET meetingPlace :
                \/ totalMeetings < N
                   /\ /\ meetingPlace' = <>
                      /\ color'[c] = ChangeColor(color[c], col)
                      /\ meetings'[c] = meetings[c] + 1
                      /\ totalMeetings' = totalMeetings + 1
                \/ totalMeetings >= N
                   /\ meetingPlace' = <<c, color[c]>>
                   /\ UNCHANGED <<color - {c}, meetings, totalMeetings>>

vars == <<color, meetings, meetingPlace, totalMeetings>>

Spec == Init /\ [][Next]_vars

\* Safety invariant: when the total number of meetings reaches N,
\* the sum of all individual meeting counters equals 2 * N
TypeOK ==
    /\ color \in [1..NumChameneoses -> Colors]
    /\ meetings \in [1..NumChameneoses -> {0}]
    /\ meetingPlace \in (SUBSET {[1..NumChameneoses] X Colors}) \cap {s: Len(s) <= 2}
    /\ totalMeetings \in Nat

TotalMeetingsInvariant ==
    \/ totalMeetings < N
       \/ totalMeetings = N /\ \A c \in 1..NumChameneoses : meetings[c] * 2 = totalMeetings

Inv == TypeOK /\ TotalMeetingsInvariant

=============================================================================