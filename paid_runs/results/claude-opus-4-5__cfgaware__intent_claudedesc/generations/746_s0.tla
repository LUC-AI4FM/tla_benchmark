---------------------------- MODULE Chameneos ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS M, N, Colors

VARIABLES creatures, mall, totalMeetings, faded

vars == <<creatures, mall, totalMeetings, faded>>

\* Colors are blue, red, yellow
Blue == "blue"
Red == "red"
Yellow == "yellow"

\* Complement function: returns the third color if different, same if identical
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF (c1 = Blue /\ c2 = Red) \/ (c1 = Red /\ c2 = Blue) THEN Yellow
    ELSE IF (c1 = Blue /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue) THEN Red
    ELSE Blue  \* Red and Yellow

\* Type invariant
TypeOK ==
    /\ creatures \in [1..M -> [color: {"blue", "red", "yellow"}, meetings: Nat]]
    /\ mall \in {<<"empty">>} \cup (1..M)
    /\ totalMeetings \in 0..N
    /\ faded \subseteq (1..M)

\* Sum of all creatures' personal meeting counts
SumMet == 
    LET Sum[i \in 0..M] ==
        IF i = 0 THEN 0
        ELSE Sum[i-1] + creatures[i].meetings
    IN Sum[M]

\* Initial state: each creature has a color and 0 meetings, mall is empty
Init ==
    /\ creatures \in [1..M -> [color: {"blue", "red", "yellow"}, meetings: {0}]]
    /\ mall = <<"empty">>
    /\ totalMeetings = 0
    /\ faded = {}

\* A creature arrives at an empty mall and waits (if meetings not exhausted)
Arrive(c) ==
    /\ c \notin faded
    /\ mall = <<"empty">>
    /\ totalMeetings < N
    /\ mall' = c
    /\ UNCHANGED <<creatures, totalMeetings, faded>>

\* A creature arrives and meets the waiting creature
Meet(c) ==
    /\ c \notin faded
    /\ mall # <<"empty">>
    /\ mall \in 1..M
    /\ c # mall
    /\ totalMeetings < N
    /\ LET waiter == mall
           newColor == Complement(creatures[c].color, creatures[waiter].color)
       IN creatures' = [creatures EXCEPT 
            ![c].color = newColor,
            ![c].meetings = @ + 1,
            ![waiter].color = newColor,
            ![waiter].meetings = @ + 1]
    /\ totalMeetings' = totalMeetings + 1
    /\ mall' = <<"empty">>
    /\ UNCHANGED faded

\* A creature fades when arriving and N meetings have occurred
Fade(c) ==
    /\ c \notin faded
    /\ totalMeetings = N
    /\ faded' = faded \cup {c}
    /\ UNCHANGED <<creatures, mall, totalMeetings>>

\* Next state relation
Next ==
    \E c \in 1..M :
        \/ Arrive(c)
        \/ Meet(c)
        \/ Fade(c)

\* Fairness: weak fairness for all creature actions
Fairness ==
    \A c \in 1..M :
        /\ WF_vars(Arrive(c))
        /\ WF_vars(Meet(c))
        /\ WF_vars(Fade(c))

\* Complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety property: when N meetings have occurred, sum equals 2*N
SafetyProperty ==
    totalMeetings = N => SumMet = 2 * N

\* Termination: all creatures eventually fade
Terminated == faded = 1..M

==========================================================================