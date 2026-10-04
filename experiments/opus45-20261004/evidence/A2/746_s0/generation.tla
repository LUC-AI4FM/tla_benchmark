---------------------------- MODULE Chameneos ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

Colors == {"blue", "red", "yellow"}

Faded == "faded"

AllColors == Colors \cup {Faded}

Creatures == 1..M

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF c1 = "blue" /\ c2 = "red" THEN "yellow"
    ELSE IF c1 = "blue" /\ c2 = "yellow" THEN "red"
    ELSE IF c1 = "red" /\ c2 = "blue" THEN "yellow"
    ELSE IF c1 = "red" /\ c2 = "yellow" THEN "blue"
    ELSE IF c1 = "yellow" /\ c2 = "blue" THEN "red"
    ELSE "blue"  \* c1 = "yellow" /\ c2 = "red"

Init ==
    /\ chameneoses \in [Creatures -> [color: Colors, meetings: {0}]]
    /\ meetingPlace = CHOOSE x : x \notin Creatures
    /\ numMeetings = 0

Empty == CHOOSE x : x \notin Creatures

IsNonFaded(c) == chameneoses[c].color # Faded

EnterMeetingPlace(c) ==
    /\ IsNonFaded(c)
    /\ meetingPlace = Empty
    /\ numMeetings < N
    /\ meetingPlace' = c
    /\ UNCHANGED <<chameneoses, numMeetings>>

FadeImmediately(c) ==
    /\ IsNonFaded(c)
    /\ meetingPlace = Empty
    /\ numMeetings = N
    /\ chameneoses' = [chameneoses EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<meetingPlace, numMeetings>>

CompleteMeeting(c) ==
    /\ IsNonFaded(c)
    /\ meetingPlace # Empty
    /\ meetingPlace # c
    /\ LET waiting == meetingPlace
           newColor == Complement(chameneoses[c].color, chameneoses[waiting].color)
       IN /\ chameneoses' = [chameneoses EXCEPT 
               ![c].color = newColor,
               ![c].meetings = @ + 1,
               ![waiting].color = newColor,
               ![waiting].meetings = @ + 1]
          /\ numMeetings' = numMeetings + 1
          /\ meetingPlace' = Empty

Meet(c) ==
    \/ EnterMeetingPlace(c)
    \/ FadeImmediately(c)
    \/ CompleteMeeting(c)

Next == \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

SumOfMeetings == 
    LET Sum[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET c == CHOOSE x \in S : TRUE
             IN chameneoses[c].meetings + Sum[S \ {c}]
    IN Sum[Creatures]

SumMet == numMeetings = N => SumOfMeetings = 2 * N

==========================================================================