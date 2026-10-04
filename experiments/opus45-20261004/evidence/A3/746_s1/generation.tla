-------------------------------- MODULE Chameneos --------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Creatures, N, Colors

VARIABLES color, meetingCount, meetingPlace, totalMeetings, faded

vars == <<color, meetingCount, meetingPlace, totalMeetings, faded>>

\* Symmetric complement function for colors
\* Assuming Colors = {Blue, Red, Yellow} with standard complement rules
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF {c1, c2} = {"Blue", "Red"} THEN "Yellow"
    ELSE IF {c1, c2} = {"Blue", "Yellow"} THEN "Red"
    ELSE IF {c1, c2} = {"Red", "Yellow"} THEN "Blue"
    ELSE c1 \* fallback

TypeOK ==
    /\ color \in [Creatures -> Colors]
    /\ meetingCount \in [Creatures -> Nat]
    /\ meetingPlace \in [waiting: BOOLEAN, creature: Creatures \cup {CHOOSE x : x \notin Creatures}]
    /\ totalMeetings \in Nat
    /\ faded \in SUBSET Creatures

Init ==
    /\ color \in [Creatures -> Colors]
    /\ meetingCount = [c \in Creatures |-> 0]
    /\ meetingPlace = [waiting |-> FALSE, creature |-> CHOOSE x : x \notin Creatures]
    /\ totalMeetings = 0
    /\ faded = {}

\* A creature arrives at an empty meeting place and waits
Arrive(c) ==
    /\ c \notin faded
    /\ totalMeetings < N
    /\ meetingPlace.waiting = FALSE
    /\ meetingPlace' = [waiting |-> TRUE, creature |-> c]
    /\ UNCHANGED <<color, meetingCount, totalMeetings, faded>>

\* A creature meets another creature that is waiting
Meet(c) ==
    /\ c \notin faded
    /\ totalMeetings < N
    /\ meetingPlace.waiting = TRUE
    /\ meetingPlace.creature /= c
    /\ LET other == meetingPlace.creature
           newColor == Complement(color[c], color[other])
       IN /\ color' = [color EXCEPT ![c] = newColor, ![other] = newColor]
          /\ meetingCount' = [meetingCount EXCEPT ![c] = @ + 1, ![other] = @ + 1]
          /\ totalMeetings' = totalMeetings + 1
          /\ meetingPlace' = [waiting |-> FALSE, creature |-> CHOOSE x : x \notin Creatures]
          /\ UNCHANGED faded

\* A creature tries to meet but the limit is reached, so it fades
Fade(c) ==
    /\ c \notin faded
    /\ totalMeetings >= N
    /\ faded' = faded \cup {c}
    /\ UNCHANGED <<color, meetingCount, meetingPlace, totalMeetings>>

Next ==
    \E c \in Creatures : Arrive(c) \/ Meet(c) \/ Fade(c)

\* Sum of all individual meeting counters
SumMeetingCounts ==
    LET RECURSIVE Sum(_)
        Sum(S) == IF S = {} THEN 0
                  ELSE LET c == CHOOSE x \in S : TRUE
                       IN meetingCount[c] + Sum(S \ {c})
    IN Sum(Creatures)

\* Safety invariant: when total meetings reaches N, sum of individual counts equals 2*N
MeetingCountInvariant ==
    totalMeetings = N => SumMeetingCounts = 2 * N

\* Additional safety invariant: total meetings never exceeds N
TotalMeetingsLimit ==
    totalMeetings <= N

\* Invariant: sum of individual counts always equals 2 * totalMeetings
CountConsistency ==
    SumMeetingCounts = 2 * totalMeetings

Spec == Init /\ [][Next]_vars

================================================================================