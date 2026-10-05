---------------------------- MODULE Chameneos ----------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS N, M

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

Colors == {"blue", "red", "yellow"}

Faded == "faded"

ColorOrFaded == Colors \cup {Faded}

Creatures == 1..M

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF c1 = "blue" THEN
        IF c2 = "red" THEN "yellow" ELSE "red"
    ELSE IF c1 = "red" THEN
        IF c2 = "blue" THEN "yellow" ELSE "blue"
    ELSE
        IF c2 = "blue" THEN "red" ELSE "blue"

TypeOK ==
    /\ chameneoses \in [Creatures -> [color: ColorOrFaded, met: Nat]]
    /\ meetingPlace \in Creatures \cup {0}
    /\ numMeetings \in 0..N

Init ==
    /\ chameneoses \in [Creatures -> [color: Colors, met: {0}]]
    /\ meetingPlace = 0
    /\ numMeetings = 0

EnterMeetingPlace(c) ==
    /\ chameneoses[c].color # Faded
    /\ meetingPlace = 0
    /\ numMeetings < N
    /\ meetingPlace' = c
    /\ UNCHANGED <<chameneoses, numMeetings>>

FadeOut(c) ==
    /\ chameneoses[c].color # Faded
    /\ meetingPlace = 0
    /\ numMeetings = N
    /\ chameneoses' = [chameneoses EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<meetingPlace, numMeetings>>

CompleteMeeting(c) ==
    /\ chameneoses[c].color # Faded
    /\ meetingPlace # 0
    /\ meetingPlace # c
    /\ LET other == meetingPlace
           newColor == Complement(chameneoses[c].color, chameneoses[other].color)
       IN
           /\ chameneoses' = [chameneoses EXCEPT 
                ![c].color = newColor,
                ![c].met = chameneoses[c].met + 1,
                ![other].color = newColor,
                ![other].met = chameneoses[other].met + 1]
           /\ meetingPlace' = 0
           /\ numMeetings' = numMeetings + 1

Meet(c) ==
    \/ EnterMeetingPlace(c)
    \/ FadeOut(c)
    \/ CompleteMeeting(c)

Next ==
    \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

SumOfMeetings ==
    LET RECURSIVE Sum(_)
        Sum(S) ==
            IF S = {} THEN 0
            ELSE LET x == CHOOSE x \in S : TRUE
                 IN chameneoses[x].met + Sum(S \ {x})
    IN Sum(Creatures)

SumMet ==
    numMeetings = N => SumOfMeetings = 2 * N

=============================================================================