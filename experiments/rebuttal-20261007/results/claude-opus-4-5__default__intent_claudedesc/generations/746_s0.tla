---------------------------- MODULE Chameneos ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS M, N, Creatures

ASSUME M \in Nat /\ M > 0
ASSUME N \in Nat /\ N >= 0
ASSUME Cardinality(Creatures) = M

VARIABLES
    color,           \* color[c] is the current color of creature c
    meetingCount,    \* meetingCount[c] is the number of meetings creature c has had
    totalMeetings,   \* total number of pairwise meetings that have occurred
    mall,            \* either "empty" or the id of a waiting creature
    faded            \* set of creatures that have faded

Colors == {"blue", "red", "yellow"}

\* Complement function: when two creatures meet, they both adopt this color
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF {c1, c2} = {"blue", "red"} THEN "yellow"
    ELSE IF {c1, c2} = {"blue", "yellow"} THEN "red"
    ELSE "blue"  \* {red, yellow}

TypeOK ==
    /\ color \in [Creatures -> Colors]
    /\ meetingCount \in [Creatures -> Nat]
    /\ totalMeetings \in Nat
    /\ totalMeetings <= N
    /\ (mall = "empty" \/ mall \in Creatures)
    /\ faded \subseteq Creatures

Init ==
    /\ color \in [Creatures -> Colors]  \* Each creature starts with some color
    /\ meetingCount = [c \in Creatures |-> 0]
    /\ totalMeetings = 0
    /\ mall = "empty"
    /\ faded = {}

\* A creature arrives at an empty mall when meetings are still possible, and waits
ArriveAndWait(c) ==
    /\ c \notin faded
    /\ mall = "empty"
    /\ totalMeetings < N
    /\ mall' = c
    /\ UNCHANGED <<color, meetingCount, totalMeetings, faded>>

\* A creature arrives and meets the waiting creature
ArriveAndMeet(c) ==
    /\ c \notin faded
    /\ mall # "empty"
    /\ mall # c  \* Can't meet yourself
    /\ mall \notin faded
    /\ totalMeetings < N
    /\ LET waiting == mall
           newColor == Complement(color[waiting], color[c])
       IN
           /\ color' = [color EXCEPT ![waiting] = newColor, ![c] = newColor]
           /\ meetingCount' = [meetingCount EXCEPT ![waiting] = @ + 1, ![c] = @ + 1]
           /\ totalMeetings' = totalMeetings + 1
           /\ mall' = "empty"
           /\ UNCHANGED faded

\* A creature arrives at the mall after N meetings have occurred and fades
ArriveAndFade(c) ==
    /\ c \notin faded
    /\ totalMeetings = N
    /\ mall = "empty"  \* Mall must be empty (no one waiting when limit reached)
    /\ faded' = faded \cup {c}
    /\ UNCHANGED <<color, meetingCount, totalMeetings, mall>>

\* The waiting creature fades when it realizes meetings are done
WaitingFades(c) ==
    /\ c \notin faded
    /\ mall = c
    /\ totalMeetings = N
    /\ faded' = faded \cup {c}
    /\ mall' = "empty"
    /\ UNCHANGED <<color, meetingCount, totalMeetings>>

Next ==
    \/ \E c \in Creatures : ArriveAndWait(c)
    \/ \E c \in Creatures : ArriveAndMeet(c)
    \/ \E c \in Creatures : ArriveAndFade(c)
    \/ \E c \in Creatures : WaitingFades(c)

\* Allow stuttering when all creatures have faded (termination)
Spec == Init /\ [][Next]_<<color, meetingCount, totalMeetings, mall, faded>>

\* Safety: When exactly N meetings have occurred, sum of personal counts = 2*N
SumMeetingCounts == 
    LET Sum[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET c == CHOOSE x \in S : TRUE
             IN meetingCount[c] + Sum[S \ {c}]
    IN Sum[Creatures]

MeetingCountInvariant ==
    totalMeetings = N => SumMeetingCounts = 2 * N

\* Combined safety invariant
Safety == TypeOK /\ MeetingCountInvariant

\* Liveness: Eventually all creatures fade (system terminates)
AllFaded == faded = Creatures

Termination == <>(AllFaded)

\* Fairness: Weak fairness on all creature actions
FairSpec == Spec /\ \A c \in Creatures : 
    /\ WF_<<color, meetingCount, totalMeetings, mall, faded>>(ArriveAndWait(c))
    /\ WF_<<color, meetingCount, totalMeetings, mall, faded>>(ArriveAndMeet(c))
    /\ WF_<<color, meetingCount, totalMeetings, mall, faded>>(ArriveAndFade(c))
    /\ WF_<<color, meetingCount, totalMeetings, mall, faded>>(WaitingFades(c))

=========================================================================