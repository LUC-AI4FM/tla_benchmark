---------------------------- MODULE ChameneosGame ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS NumChameneos, Colors, N

VARIABLES colors, meetings, totalMeetings

Init == /\ colors \in [1..NumChameneos -> Colors]
        /\ meetings \in [1..NumChameneos -> 0]
        /\ totalMeetings = 0

ColorChange(c1, c2) ==
    IF c1 = c2 THEN c1 ELSE CHOOSE c \in Colors : c # c1 /\ c # c2

Next ==
    LET cham1 == CHOOSE i \in 1..NumChameneos : TRUE
        cham2 == CHOOSE j \in 1..NumChameneos \ {cham1} : colors[cham1] = colors[j]
        newColor == ColorChange(colors[cham1], colors[cham2])
    IN
    /\ IF totalMeetings < N THEN
            \/ /\ meetings' = [meetings EXCEPT ![cham1] = meetings[cham1] + 1,
                                             ![cham2] = meetings[cham2] + 1]
               /\ colors' = [colors EXCEPT ![cham1] = newColor, ![cham2] = newColor]
               /\ totalMeetings' = totalMeetings + 1
           \/ /\ meetings' = meetings
              /\ colors' = colors
              /\ totalMeetings' = totalMeetings
       ELSE
            /\ meetings' = meetings
            /\ colors' = colors
            /\ totalMeetings' = totalMeetings

Spec == Init /\ [][Next]_<<colors, meetings, totalMeetings>>

SafetyInvariant ==
    \A c \in Colors : Cardinality({i \in 1..NumChameneos : colors[i] = c}) <= NumChameneos

TotalMeetingsArithmeticProperty ==
    \/ totalMeetings < N
    \/ totalMeetings = N /\ \E meetings' \in [1..NumChameneos -> Nat] :
         (\A i \in 1..NumChameneos : meetings'[i] = meetings[i]) /\ Sum(meetings') = 2 * N

Invariant == SafetyInvariant /\ TotalMeetingsArithmeticProperty

=============================================================================