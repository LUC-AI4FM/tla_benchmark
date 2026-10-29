---------------------------- MODULE Chameneos ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, \* total number of meetings allowed before chameneoses fade
          M  \* number of chameneoses

ASSUME N \in Nat /\ M \in Nat \ {0}

Color == {"blue", "red", "yellow"}

Faded == CHOOSE c : c \notin Color

MeetingPlaceEmpty == CHOOSE u : u \notin 1..M

ID == 1..M

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in Color \ {c1, c2} : TRUE

TypeOK ==
    /\ chameneoses \in [ID -> (Color \cup {Faded}) \X (0..N)]
    /\ meetingPlace \in ID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in 0..N

Init ==
    /\ chameneoses \in [ID -> Color \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty
    THEN IF numMeetings < N
         THEN \* chameneos enters the meeting place and waits
              /\ meetingPlace' = cid
              /\ UNCHANGED <<chameneoses, numMeetings>>
         ELSE \* no more meetings allowed: chameneos fades
              /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
              /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE \* meet the waiting chameneos
         /\ meetingPlace /= cid
         /\ meetingPlace' = MeetingPlaceEmpty
         /\ numMeetings' = numMeetings + 1
         /\ LET newColor == Complement(chameneoses[cid][1],
                                       chameneoses[meetingPlace][1])
            IN chameneoses' =
                 [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                     ![meetingPlace] = <<newColor, @[2] + 1>>]

Next ==
    \E c \in ID : /\ chameneoses[c][1] /= Faded
                  /\ Meet(c)

Spec == Init /\ [][Next]_vars

RECURSIVE SumMeetings(_)
SumMeetings(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN chameneoses[x][2] + SumMeetings(S \ {x})

SumMet == numMeetings = N => SumMeetings(ID) = 2 * N

=============================================================================