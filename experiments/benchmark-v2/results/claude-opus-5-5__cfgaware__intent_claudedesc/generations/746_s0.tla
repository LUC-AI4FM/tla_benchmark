------------------------------- MODULE Chameneos -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N,                 \* Total number of meetings allowed
          M,                 \* Number of chameneos creatures
          Faded,             \* Color value representing a faded creature
          MeetingPlaceEmpty  \* Value representing an empty meeting place

ASSUME N \in Nat /\ M \in Nat \ {0}

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

Color == {"blue", "red", "yellow"}

ChameneosID == 1..M

MeetingPlace == ChameneosID \cup {MeetingPlaceEmpty}

Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE CHOOSE c \in Color : c # c1 /\ c # c2

TypeOK ==
    /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0..N)]
    /\ meetingPlace \in MeetingPlace
    /\ numMeetings \in 0..N

Init ==
    /\ chameneoses \in [ChameneosID -> Color \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty
    THEN IF numMeetings < N
         THEN \* Enter the empty mall and wait
              /\ meetingPlace' = cid
              /\ UNCHANGED <<chameneoses, numMeetings>>
         ELSE \* All meetings done: fade permanently
              /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
              /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE \* Someone else is waiting: meet them
         /\ meetingPlace # cid
         /\ meetingPlace' = MeetingPlaceEmpty
         /\ numMeetings' = numMeetings + 1
         /\ LET other    == meetingPlace
                newColor == Complement(chameneoses[cid][1], chameneoses[other][1])
            IN  chameneoses' =
                  [chameneoses EXCEPT ![cid]   = <<newColor, @[2] + 1>>,
                                      ![other] = <<newColor, @[2] + 1>>]

Next ==
    \E c \in ChameneosID :
        /\ chameneoses[c][1] # Faded
        /\ Meet(c)

Spec == Init /\ [][Next]_vars

RECURSIVE SumSet(_)
SumSet(S) ==
    IF S = {}
    THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN  chameneoses[x][2] + SumSet(S \ {x})

SumMet == (numMeetings = N) => (SumSet(ChameneosID) = 2 * N)

=============================================================================