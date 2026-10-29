------------------------------ MODULE Chameneos ------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N,    \* global limit on the total number of meetings
          M     \* number of chameneoses

ASSUME /\ N \in Nat \ {0}
       /\ M \in Nat \ {0}

Color == {"blue", "red", "yellow"}
Faded == "faded"

ChameneosID == 1..M
MeetingPlaceEmpty == 0

VARIABLES chameneoses,   \* cid -> <<color, individual meeting count>>
          meetingPlace,  \* single shared meeting-place slot
          numMeetings    \* total number of meetings

vars == <<chameneoses, meetingPlace, numMeetings>>

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in Color \ {c1, c2} : TRUE

TypeOK ==
    /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X Nat]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in 0..N

Init ==
    /\ chameneoses \in [ChameneosID -> Color \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty
    THEN IF numMeetings < N
         THEN \* enter the empty meeting place and wait
              /\ meetingPlace' = cid
              /\ UNCHANGED <<chameneoses, numMeetings>>
         ELSE \* limit reached: the creature fades
              /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
              /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE \* meet the waiting creature
         /\ meetingPlace /= cid
         /\ meetingPlace' = MeetingPlaceEmpty
         /\ numMeetings' = numMeetings + 1
         /\ LET newColor == Complement(chameneoses[cid][1],
                                       chameneoses[meetingPlace][1])
            IN  chameneoses' =
                  [chameneoses EXCEPT ![cid]          = <<newColor, @[2] + 1>>,
                                      ![meetingPlace] = <<newColor, @[2] + 1>>]

Next ==
    \E c \in ChameneosID :
        /\ chameneoses[c][1] /= Faded
        /\ Meet(c)

Spec == Init /\ [][Next]_vars

\* Sum of all individual meeting counters
SumMet ==
    LET S[i \in 0..M] ==
            IF i = 0 THEN 0 ELSE chameneoses[i][2] + S[i - 1]
    IN  S[M]

\* When the total number of meetings reaches N, the counters sum to 2 * N
SumMeetings == (numMeetings = N) => (SumMet = 2 * N)

THEOREM Spec => [](TypeOK /\ SumMeetings)
=============================================================================