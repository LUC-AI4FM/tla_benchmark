------------------------------ MODULE Chameneos ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N,   \* total number of meetings allowed
          M    \* number of chameneoses

ASSUME /\ N \in Nat /\ N > 0
       /\ M \in Nat /\ M > 0

ChameneosID == 1..M

Color == {"blue", "red", "yellow"}

Faded == "faded"

\* 0 denotes an empty meeting place
MeetingPlaceValues == {0} \cup ChameneosID

VARIABLES chameneoses,   \* chameneoses[c] = <<color, number of meetings>>
          meetingPlace,  \* 0 (empty) or the id of the waiting chameneos
          numMeetings    \* total number of meetings so far

vars == <<chameneoses, meetingPlace, numMeetings>>

\* Symmetric complement rule
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in Color \ {c1, c2} : TRUE

TypeOK ==
    /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X Nat]
    /\ meetingPlace \in MeetingPlaceValues
    /\ numMeetings \in 0..N

Init ==
    /\ chameneoses \in [ChameneosID -> Color \X {0}]
    /\ meetingPlace = 0
    /\ numMeetings = 0

Meet(cid) ==
    IF meetingPlace = 0
    THEN IF numMeetings < N
         THEN \* enter the empty meeting place and wait
              /\ meetingPlace' = cid
              /\ UNCHANGED <<chameneoses, numMeetings>>
         ELSE \* the limit has been reached: fade
              /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
              /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE \* another chameneos is waiting: meet it
         /\ meetingPlace /= cid
         /\ meetingPlace' = 0
         /\ numMeetings' = numMeetings + 1
         /\ LET other == meetingPlace
                newColor == Complement(chameneoses[cid][1],
                                       chameneoses[other][1])
            IN chameneoses' =
                 [chameneoses EXCEPT
                    ![cid]   = <<newColor, @[2] + 1>>,
                    ![other] = <<newColor, @[2] + 1>>]

Next ==
    \E cid \in ChameneosID :
        /\ chameneoses[cid][1] /= Faded
        /\ Meet(cid)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Sum of all individual meeting counters

RECURSIVE SumSet(_)
SumSet(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN chameneoses[x][2] + SumSet(S \ {x})

SumMeet == SumSet(ChameneosID)

\* Safety: when total meetings reach N, the individual counters sum to 2 * N
SumMeetings == (numMeetings = N) => (SumMeet = 2 * N)

=============================================================================