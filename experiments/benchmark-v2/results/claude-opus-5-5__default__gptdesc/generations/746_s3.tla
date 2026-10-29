---------------------------- MODULE Chameneos ----------------------------
EXTENDS Integers, Naturals

CONSTANTS N,   \* global limit on the total number of meetings
          M    \* number of chameneoses

ASSUME N \in Nat /\ M \in Nat \ {0}

ChameneosID == 1..M

MeetingPlaceEmpty == 0

BasicColor == {"blue", "red", "yellow"}
Color == BasicColor \cup {"faded"}

\* Symmetric complement rule
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in BasicColor : c # c1 /\ c # c2

VARIABLES color,        \* color[c] : current color of chameneos c
          count,        \* count[c] : number of meetings c has taken part in
          meetingPlace, \* the shared meeting-place slot (0 = empty)
          numMeetings   \* total number of meetings so far

vars == <<color, count, meetingPlace, numMeetings>>

TypeOK ==
    /\ color \in [ChameneosID -> Color]
    /\ count \in [ChameneosID -> Nat]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in 0..N

Init ==
    /\ color \in [ChameneosID -> BasicColor]
    /\ count = [c \in ChameneosID |-> 0]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty
    THEN IF numMeetings < N
         THEN \* enter the empty meeting place and wait
              /\ meetingPlace' = cid
              /\ UNCHANGED <<color, count, numMeetings>>
         ELSE \* limit reached: the creature fades
              /\ color' = [color EXCEPT ![cid] = "faded"]
              /\ UNCHANGED <<count, meetingPlace, numMeetings>>
    ELSE \* someone else is waiting: meet them
         /\ meetingPlace # cid
         /\ meetingPlace' = MeetingPlaceEmpty
         /\ numMeetings' = numMeetings + 1
         /\ LET other    == meetingPlace
                newColor == Complement(color[cid], color[other])
            IN  /\ color' = [color EXCEPT ![cid] = newColor,
                                          ![other] = newColor]
                /\ count' = [count EXCEPT ![cid] = @ + 1,
                                          ![other] = @ + 1]

Next ==
    \E c \in ChameneosID :
        /\ color[c] # "faded"
        /\ Meet(c)

Spec == Init /\ [][Next]_vars

\* Sum of all individual meeting counters
RECURSIVE SumFrom(_, _)
SumFrom(f, i) == IF i > M THEN 0 ELSE f[i] + SumFrom(f, i + 1)

TotalCount == SumFrom(count, 1)

\* When the total number of meetings reaches N, the counters sum to 2 * N
SumMeet == (numMeetings = N) => (TotalCount = 2 * N)

THEOREM Spec => [](TypeOK /\ SumMeet)
=============================================================================