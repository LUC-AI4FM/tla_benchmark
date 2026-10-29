---------------------------- MODULE Chameneos ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ M \in Nat /\ M >= 2

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

Color == {"blue", "red", "yellow"}

ChameneosID == 1..M

MeetingPlace == ChameneosID \cup {MeetingPlaceEmpty}

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in Color : c \notin {c1, c2}

TypeOK ==
    /\ chameneoses \in [ChameneosID -> [color : Color \cup {Faded}, met : 0..N]]
    /\ meetingPlace \in MeetingPlace
    /\ numMeetings \in 0..N

RECURSIVE SumSet(_)
SumSet(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN chameneoses[x].met + SumSet(S \ {x})

SumMet ==
    numMeetings = N => SumSet(ChameneosID) = 2 * N

Init ==
    /\ chameneoses \in [ChameneosID -> [color : Color, met : {0}]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty
    THEN IF numMeetings < N
         THEN /\ meetingPlace' = cid
              /\ UNCHANGED <<chameneoses, numMeetings>>
         ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid].color = Faded]
              /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE /\ meetingPlace /= cid
         /\ meetingPlace' = MeetingPlaceEmpty
         /\ numMeetings' = numMeetings + 1
         /\ LET other == meetingPlace
                newColor == Complement(chameneoses[cid].color,
                                       chameneoses[other].color)
            IN chameneoses' =
                 [chameneoses EXCEPT
                    ![cid]   = [color |-> newColor, met |-> @.met + 1],
                    ![other] = [color |-> newColor, met |-> @.met + 1]]

Next ==
    \E cid \in ChameneosID :
        /\ chameneoses[cid].color /= Faded
        /\ Meet(cid)

Spec == Init /\ [][Next]_vars

=============================================================================