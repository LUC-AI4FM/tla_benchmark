------------------------------- MODULE Chameneos -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS M, N
ASSUME M \in Nat /\ M > 0
ASSUME N \in Nat /\ N > 0

VARIABLES colors, meetings, totalMeetings, faded

ColorSet == {blue, red, yellow}

ComplementColor(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in ColorSet : c /= c1 /\ c /= c2

Init ==
    /\ colors \in [1..M -> ColorSet]
    /\ meetings \in [1..M -> 0]
    /\ totalMeetings = 0
    /\ faded = {}

Next ==
    \/ /\ \E i \in 1..M : \neg (i \in DOMAIN colors) /\ i \notin faded
       /\ \/ /\ totalMeetings < N
              /\ \E j \in 1..M : j \in DOMAIN colors /\ j /= i
                 /\ meetings[j] < N
                 /\ LET c_i == colors[i]
                    c_j == colors[j]
                    newColor == ComplementColor(c_i, c_j)
                 IN \/ /\ colors' = [colors EXCEPT ![i] = newColor, ![j] = newColor]
                    /\ meetings' = [meetings EXCEPT ![i] = meetings[i] + 1, ![j] = meetings[j] + 1]
                    /\ totalMeetings' = totalMeetings + 1
                    /\ faded' = faded
           \/ /\ totalMeetings >= N
              /\ colors' = [colors EXCEPT ![\E i \in 1..M : i \in DOMAIN colors] = UNCHANGED]
              /\ meetings' = meetings
              /\ totalMeetings' = totalMeetings
              /\ faded' = faded \cup {i}
    \/ /\ \A i \in 1..M : (i \notin DOMAIN colors) => i \in faded
       /\ colors' = colors
       /\ meetings' = meetings
       /\ totalMeetings' = totalMeetings
       /\ faded' = faded

Spec ==
    /\ Init
    /\ [][Next]_<<colors, meetings, totalMeetings, faded>>
    /\ <><\A i \in 1..M : i \in faded>_<<colors, meetings, totalMeetings, faded>>

Safety ==
    \/ totalMeetings >= N => \Sum(i \in 1..M) meetings[i] = 2 * N

Liveness ==
    <>[](\A i \in 1..M : i \in faded)

TypeOK ==
    /\ colors \in [1..M -> ColorSet]
    /\ meetings \in [1..M -> Nat]
    /\ totalMeetings \in Nat
    /\ faded \subseteq (1..M)

CompleteSpec == Spec /\ []Safety /\ Liveness /\ []TypeOK

=============================================================================