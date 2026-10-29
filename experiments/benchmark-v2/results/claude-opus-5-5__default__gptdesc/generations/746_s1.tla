---------------------------- MODULE Chameneos ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,          \* global limit on the total number of meetings
    NumChams    \* number of chameneoses taking part in the game

ASSUME /\ N \in Nat
       /\ N > 0
       /\ NumChams \in Nat
       /\ NumChams >= 2

ChameneosID == 1..NumChams

\* Sentinel value marking an empty meeting place
MeetingPlaceEmpty == 0

Colors == {"blue", "red", "yellow"}
Color  == Colors \cup {"faded"}

\* Symmetric complement rule: same colours stay the same,
\* different colours both become the third colour.
Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE CHOOSE c \in Colors : c # c1 /\ c # c2

VARIABLES
    chameneoses,    \* chameneoses[cid] = <<colour, individual meeting count>>
    meetingPlace,   \* single shared slot: either empty or the waiting chameneos
    numMeetings     \* total number of meetings so far

vars == <<chameneoses, meetingPlace, numMeetings>>

TypeOK ==
    /\ chameneoses \in [ChameneosID -> Color \X Nat]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in 0..N

Init ==
    /\ chameneoses \in [ChameneosID -> Colors \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

\* A chameneos with identifier cid attempts to meet.
Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty
    THEN IF numMeetings < N
         THEN \* enter the empty meeting place and wait for a partner
              /\ meetingPlace' = cid
              /\ UNCHANGED <<chameneoses, numMeetings>>
         ELSE \* the meeting limit has been reached: the chameneos fades
              /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<"faded", @[2]>>]
              /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE \* another chameneos is waiting: meet it
         /\ meetingPlace # cid
         /\ meetingPlace' = MeetingPlaceEmpty
         /\ numMeetings' = numMeetings + 1
         /\ LET newColor == Complement(chameneoses[cid][1],
                                       chameneoses[meetingPlace][1])
            IN chameneoses' =
                 [chameneoses EXCEPT
                    ![cid]          = <<newColor, @[2] + 1>>,
                    ![meetingPlace] = <<newColor, @[2] + 1>>]

Next ==
    \E cid \in {x \in ChameneosID : chameneoses[x][1] # "faded"} : Meet(cid)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Sum of all individual meeting counters

RECURSIVE SumSet(_)
SumSet(S) ==
    IF S = {}
    THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN chameneoses[x][2] + SumSet(S \ {x})

SumMet == SumSet(ChameneosID)

\* When the total number of meetings reaches N, every meeting has been
\* counted twice (once for each participant).
SumMeetings == (numMeetings = N) => (SumMet = 2 * N)

THEOREM Spec => [](TypeOK /\ SumMeetings)
=============================================================================