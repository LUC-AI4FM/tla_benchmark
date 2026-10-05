---------------------------- MODULE Chameneos ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    Creatures,      \* The set of creature identifiers
    Colors,         \* The set of possible colors (e.g., {Blue, Red, Yellow})
    N               \* Maximum number of meetings allowed

ASSUME N \in Nat
ASSUME Colors # {}
ASSUME Creatures # {}

VARIABLES
    color,          \* color[c] = current color of creature c
    meetingCount,   \* meetingCount[c] = number of meetings creature c has participated in
    meetingPlace,   \* Either <<>> (empty) or <<c>> where c is waiting creature
    totalMeetings,  \* Total number of completed meetings so far
    faded           \* faded[c] = TRUE if creature c has faded

vars == <<color, meetingCount, meetingPlace, totalMeetings, faded>>

\* Symmetric complement function for colors
\* When two creatures of the same color meet, they stay the same
\* When two creatures of different colors meet, they both become the third color
\* This models the classic complement rule
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in Colors : c # c1 /\ c # c2

TypeOK ==
    /\ color \in [Creatures -> Colors]
    /\ meetingCount \in [Creatures -> Nat]
    /\ meetingPlace \in UNION {[1..k -> Creatures] : k \in 0..1}
    /\ totalMeetings \in Nat
    /\ faded \in [Creatures -> BOOLEAN]

\* Initial state: all creatures have some color, no meetings yet, meeting place empty
Init ==
    /\ color \in [Creatures -> Colors]
    /\ meetingCount = [c \in Creatures |-> 0]
    /\ meetingPlace = <<>>
    /\ totalMeetings = 0
    /\ faded = [c \in Creatures |-> FALSE]

\* A creature enters the empty meeting place to wait
Enter(c) ==
    /\ ~faded[c]
    /\ meetingPlace = <<>>
    /\ totalMeetings < N
    /\ meetingPlace' = <<c>>
    /\ UNCHANGED <<color, meetingCount, totalMeetings, faded>>

\* A creature meets another creature already waiting in the meeting place
Meet(c) ==
    /\ ~faded[c]
    /\ meetingPlace # <<>>
    /\ LET waiting == meetingPlace[1]
           newColor == Complement(color[c], color[waiting])
       IN
       /\ c # waiting
       /\ totalMeetings < N
       /\ color' = [color EXCEPT ![c] = newColor, ![waiting] = newColor]
       /\ meetingCount' = [meetingCount EXCEPT ![c] = @ + 1, ![waiting] = @ + 1]
       /\ meetingPlace' = <<>>
       /\ totalMeetings' = totalMeetings + 1
       /\ UNCHANGED faded

\* A creature tries to enter when limit is reached and fades
FadeOnEnter(c) ==
    /\ ~faded[c]
    /\ totalMeetings >= N
    /\ meetingPlace = <<>>
    /\ faded' = [faded EXCEPT ![c] = TRUE]
    /\ UNCHANGED <<color, meetingCount, meetingPlace, totalMeetings>>

\* A creature tries to meet when limit is reached and fades
FadeOnMeet(c) ==
    /\ ~faded[c]
    /\ meetingPlace # <<>>
    /\ c # meetingPlace[1]
    /\ totalMeetings >= N
    /\ faded' = [faded EXCEPT ![c] = TRUE]
    /\ UNCHANGED <<color, meetingCount, meetingPlace, totalMeetings>>

\* A waiting creature fades when limit is reached
FadeWhileWaiting(c) ==
    /\ ~faded[c]
    /\ meetingPlace = <<c>>
    /\ totalMeetings >= N
    /\ faded' = [faded EXCEPT ![c] = TRUE]
    /\ meetingPlace' = <<>>
    /\ UNCHANGED <<color, meetingCount, totalMeetings>>

Next ==
    \E c \in Creatures :
        \/ Enter(c)
        \/ Meet(c)
        \/ FadeOnEnter(c)
        \/ FadeOnMeet(c)
        \/ FadeWhileWaiting(c)

\* Helper function to sum meeting counts
SumMeetingCounts ==
    LET RECURSIVE Sum(_)
        Sum(S) == IF S = {} THEN 0
                  ELSE LET c == CHOOSE x \in S : TRUE
                       IN meetingCount[c] + Sum(S \ {c})
    IN Sum(Creatures)

\* Safety property: when total meetings reaches N, sum of individual counts equals 2*N
\* (Each meeting increments two creatures' counts, so sum should be 2*totalMeetings)
MeetingCountInvariant ==
    totalMeetings = N => SumMeetingCounts = 2 * N

\* General invariant that sum always equals 2 * totalMeetings
MeetingCountConsistency ==
    SumMeetingCounts = 2 * totalMeetings

Spec == Init /\ [][Next]_vars

==========================================================================