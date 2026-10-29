------------------------------ MODULE Chameneos ------------------------------
EXTENDS Integers, Naturals

CONSTANTS N, \* total number of meetings allowed before chameneoses fade
          M  \* number of chameneoses

ASSUME /\ N \in Nat /\ N > 0
       /\ M \in Nat /\ M > 0

VARIABLES chameneoses,  \* ID -> <<color, personal meeting count>>
          meetingPlace, \* the waiting chameneos, or MeetingPlaceEmpty
          numMeetings   \* global count of completed meetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1..M

Color == {"blue", "red", "yellow"}

Faded == CHOOSE c : c \notin Color

MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* Complement of two distinct colors is the third; of identical colors, the same color.
Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE CHOOSE c \in Color \ {c1, c2} : TRUE

TypeOK ==
    /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0..N)]
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
         ELSE \* no more meetings allowed: fade
              /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
              /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE \* meet the waiting chameneos
         /\ meetingPlace /= cid
         /\ meetingPlace' = MeetingPlaceEmpty
         /\ numMeetings' = numMeetings + 1
         /\ LET newColor == Complement(chameneoses[cid][1],
                                       chameneoses[meetingPlace][1])
            IN chameneoses' =
                 [chameneoses EXCEPT ![cid]          = <<newColor, @[2] + 1>>,
                                     ![meetingPlace] = <<newColor, @[2] + 1>>]

Next ==
    \E c \in ChameneosID :
        /\ chameneoses[c][1] /= Faded
        /\ Meet(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

RECURSIVE SumUpTo(_)
SumUpTo(k) == IF k = 0 THEN 0 ELSE chameneoses[k][2] + SumUpTo(k - 1)

\* Once all N meetings have happened, the individual meeting counts sum to 2*N.
SumMet == numMeetings = N => SumUpTo(M) = 2 * N

THEOREM Spec => [](TypeOK /\ SumMet)

=============================================================================