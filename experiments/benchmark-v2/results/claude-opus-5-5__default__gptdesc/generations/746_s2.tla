---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NAssump == N \in Nat \ {0}
ASSUME MAssump == M \in Nat \ {0}

ChameneosID == 1..M

MeetingPlaceEmpty == 0

Color == {"blue", "red", "yellow", "faded"}

LiveColor == Color \ {"faded"}

Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE CHOOSE c \in Color \ {c1, c2, "faded"} : TRUE

VARIABLES
    chameneoses,
    meetingPlace,
    numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

TypeOK ==
    /\ chameneoses \in [ChameneosID -> Color \X Nat]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in 0..N

Init ==
    /\ chameneoses \in [ChameneosID -> LiveColor \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty
    THEN IF numMeetings < N
         THEN /\ meetingPlace' = cid
              /\ UNCHANGED <<chameneoses, numMeetings>>
         ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<"faded", @[2]>>]
              /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE /\ meetingPlace # cid
         /\ meetingPlace' = MeetingPlaceEmpty
         /\ numMeetings' = numMeetings + 1
         /\ LET newColor == Complement(chameneoses[cid][1],
                                       chameneoses[meetingPlace][1])
            IN chameneoses' =
                 [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                     ![meetingPlace] = <<newColor, @[2] + 1>>]

Next ==
    \E c \in {x \in ChameneosID : chameneoses[x][1] # "faded"} : Meet(c)

Spec == Init /\ [][Next]_vars

RECURSIVE SumSet(_)
SumSet(S) ==
    IF S = {}
    THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN chameneoses[x][2] + SumSet(S \ {x})

SumMeetings == SumSet(ChameneosID)

SumMeet == (numMeetings = N) => (SumMeetings = 2 * N)

THEOREM Spec => [](TypeOK /\ SumMeet)
====