---------------------------- MODULE Chameneos ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Creatures,      \* Set of creature identifiers
    Colors,         \* Set of possible colors (e.g., {"blue", "red", "yellow"})
    N,              \* Maximum number of meetings
    Complement      \* Complement function: [Colors \X Colors -> Colors]

VARIABLES
    color,          \* color[c] = current color of creature c
    meetingCount,   \* meetingCount[c] = number of meetings creature c has participated in
    meetingPlace,   \* Either <<>> (empty) or <<c, col>> where c is waiting with color col
    totalMeetings,  \* Total number of completed meetings
    faded           \* faded[c] = TRUE if creature c has faded

vars == <<color, meetingCount, meetingPlace, totalMeetings, faded>>

\* Type invariant
TypeOK ==
    /\ color \in [Creatures -> Colors]
    /\ meetingCount \in [Creatures -> Nat]
    /\ meetingPlace \in {<<>>} \cup (Creatures \X Colors)
    /\ totalMeetings \in Nat
    /\ faded \in [Creatures -> BOOLEAN]

\* Initial state
Init ==
    /\ color \in [Creatures -> Colors]
    /\ meetingCount = [c \in Creatures |-> 0]
    /\ meetingPlace = <<>>
    /\ totalMeetings = 0
    /\ faded = [c \in Creatures |-> FALSE]

\* A creature enters an empty meeting place
Enter(c) ==
    /\ ~faded[c]
    /\ meetingPlace = <<>>
    /\ totalMeetings < N
    /\ meetingPlace' = <<c, color[c]>>
    /\ UNCHANGED <<color, meetingCount, totalMeetings, faded>>

\* A creature meets another creature waiting in the meeting place
Meet(c) ==
    /\ ~faded[c]
    /\ meetingPlace # <<>>
    /\ meetingPlace[1] # c      \* Cannot meet yourself
    /\ totalMeetings < N
    /\ LET other == meetingPlace[1]
           otherColor == meetingPlace[2]
           newColor == Complement[color[c], otherColor]
       IN
           /\ color' = [color EXCEPT ![c] = newColor, ![other] = newColor]
           /\ meetingCount' = [meetingCount EXCEPT ![c] = @ + 1, ![other] = @ + 1]
           /\ meetingPlace' = <<>>
           /\ totalMeetings' = totalMeetings + 1
           /\ UNCHANGED faded

\* A creature tries to enter when limit is reached and fades
FadeEnter(c) ==
    /\ ~faded[c]
    /\ meetingPlace = <<>>
    /\ totalMeetings >= N
    /\ faded' = [faded EXCEPT ![c] = TRUE]
    /\ UNCHANGED <<color, meetingCount, meetingPlace, totalMeetings>>

\* A creature tries to meet when limit is reached and fades
FadeMeet(c) ==
    /\ ~faded[c]
    /\ meetingPlace # <<>>
    /\ meetingPlace[1] # c
    /\ totalMeetings >= N
    /\ faded' = [faded EXCEPT ![c] = TRUE]
    /\ UNCHANGED <<color, meetingCount, meetingPlace, totalMeetings>>

\* The waiting creature fades when limit is reached
FadeWaiting(c) ==
    /\ ~faded[c]
    /\ meetingPlace # <<>>
    /\ meetingPlace[1] = c
    /\ totalMeetings >= N
    /\ faded' = [faded EXCEPT ![c] = TRUE]
    /\ meetingPlace' = <<>>
    /\ UNCHANGED <<color, meetingCount, totalMeetings>>

\* Next state relation
Next ==
    \E c \in Creatures:
        \/ Enter(c)
        \/ Meet(c)
        \/ FadeEnter(c)
        \/ FadeMeet(c)
        \/ FadeWaiting(c)

\* Sum of all individual meeting counts
SumMeetingCounts ==
    LET Sum[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET c == CHOOSE x \in S : TRUE
             IN meetingCount[c] + Sum[S \ {c}]
    IN Sum[Creatures]

\* Safety property: when total meetings reaches N, sum of individual counts equals 2*N
MeetingCountInvariant ==
    totalMeetings = N => SumMeetingCounts = 2 * N

\* Temporal specification without fairness
Spec == Init /\ [][Next]_vars

==========================================================================