---------------------------- MODULE Chameneos ----------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
    Creatures,      \* Set of creature identifiers
    Colors,         \* Set of possible colors (e.g., {blue, red, yellow})
    N,              \* Maximum number of meetings
    Complement      \* Complement function: Colors × Colors -> Colors

ASSUME N \in Nat
ASSUME Complement \in [Colors \X Colors -> Colors]
\* Symmetry: Complement[c1, c2] = Complement[c2, c1]
ASSUME \A c1, c2 \in Colors : Complement[c1, c2] = Complement[c2, c1]
\* Same color complement: Complement[c, c] = c
ASSUME \A c \in Colors : Complement[c, c] = c

VARIABLES
    color,          \* color[c] = current color of creature c
    meetCount,      \* meetCount[c] = number of meetings creature c has participated in
    meetingPlace,   \* Either empty ({}) or contains one creature waiting
    totalMeetings,  \* Total number of completed meetings
    faded           \* faded[c] = TRUE if creature c has faded

vars == <<color, meetCount, meetingPlace, totalMeetings, faded>>

TypeOK ==
    /\ color \in [Creatures -> Colors]
    /\ meetCount \in [Creatures -> Nat]
    /\ meetingPlace \in SUBSET Creatures
    /\ Cardinality(meetingPlace) <= 1
    /\ totalMeetings \in Nat
    /\ totalMeetings <= N
    /\ faded \in [Creatures -> BOOLEAN]

Init ==
    /\ color \in [Creatures -> Colors]      \* Each creature starts with some color
    /\ meetCount = [c \in Creatures |-> 0]  \* No meetings yet
    /\ meetingPlace = {}                     \* Meeting place is empty
    /\ totalMeetings = 0                     \* No completed meetings
    /\ faded = [c \in Creatures |-> FALSE]  \* No creature has faded

\* A creature enters the empty meeting place to wait
Enter(c) ==
    /\ ~faded[c]
    /\ meetingPlace = {}
    /\ totalMeetings < N
    /\ meetingPlace' = {c}
    /\ UNCHANGED <<color, meetCount, totalMeetings, faded>>

\* A creature meets another creature waiting in the meeting place
Meet(c1, c2) ==
    /\ ~faded[c1]
    /\ ~faded[c2]
    /\ c1 # c2
    /\ meetingPlace = {c2}
    /\ totalMeetings < N
    /\ LET newColor == Complement[color[c1], color[c2]]
       IN
        /\ color' = [color EXCEPT ![c1] = newColor, ![c2] = newColor]
        /\ meetCount' = [meetCount EXCEPT ![c1] = @ + 1, ![c2] = @ + 1]
        /\ meetingPlace' = {}
        /\ totalMeetings' = totalMeetings + 1
        /\ UNCHANGED faded

\* A creature tries to enter but meetings are exhausted, so it fades
Fade(c) ==
    /\ ~faded[c]
    /\ totalMeetings >= N
    /\ faded' = [faded EXCEPT ![c] = TRUE]
    /\ UNCHANGED <<color, meetCount, meetingPlace, totalMeetings>>

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c1, c2 \in Creatures : Meet(c1, c2)
    \/ \E c \in Creatures : Fade(c)

Spec == Init /\ [][Next]_vars

\* Safety invariant: when total meetings reaches N, sum of individual counts equals 2*N
\* Each meeting involves 2 creatures, each incrementing their count by 1

RECURSIVE SumMeetCounts(_)
SumMeetCounts(S) ==
    IF S = {} THEN 0
    ELSE LET c == CHOOSE x \in S : TRUE
         IN meetCount[c] + SumMeetCounts(S \ {c})

MeetingCountInvariant ==
    totalMeetings = N => SumMeetCounts(Creatures) = 2 * N

\* Additional invariant: sum of meeting counts always equals 2 * totalMeetings
MeetingCountConsistency ==
    SumMeetCounts(Creatures) = 2 * totalMeetings

==========================================================================