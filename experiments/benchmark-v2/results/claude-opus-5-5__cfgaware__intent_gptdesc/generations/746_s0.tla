---------------------------- MODULE Chameneos ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, M

ASSUME N \in Nat \ {0}
ASSUME M \in Nat \ {0}

ChameneosID == 1 .. M

Color == {"blue", "red", "yellow"}

Faded == CHOOSE c : c \notin Color

MeetingPlaceEmpty == CHOOSE x : x \notin ChameneosID

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

TypeOK ==
    /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in 0 .. N

(* Deterministic, symmetric colour-transition function *)
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in Color \ {c1, c2} : TRUE

Init ==
    /\ chameneoses \in [ChameneosID -> Color \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty
    THEN IF numMeetings < N
         THEN (* enter the empty meeting place and wait *)
              /\ meetingPlace' = cid
              /\ UNCHANGED <<chameneoses, numMeetings>>
         ELSE (* budget exhausted: fade *)
              /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
              /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE IF meetingPlace = cid
         THEN (* the waiting agent may only leave by fading once budget is exhausted *)
              /\ numMeetings >= N
              /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
              /\ meetingPlace' = MeetingPlaceEmpty
              /\ UNCHANGED numMeetings
         ELSE IF numMeetings < N
              THEN (* meet the waiting agent *)
                   LET other    == meetingPlace
                       newColor == Complement(chameneoses[cid][1],
                                              chameneoses[other][1])
                   IN /\ chameneoses' =
                            [chameneoses EXCEPT
                               ![cid]   = <<newColor, @[2] + 1>>,
                               ![other] = <<newColor, @[2] + 1>>]
                      /\ meetingPlace' = MeetingPlaceEmpty
                      /\ numMeetings' = numMeetings + 1
              ELSE (* budget exhausted: fade *)
                   /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
                   /\ UNCHANGED <<meetingPlace, numMeetings>>

AllFaded == \A c \in ChameneosID : chameneoses[c][1] = Faded

Terminating == AllFaded /\ UNCHANGED vars

Next ==
    \/ \E c \in ChameneosID :
          /\ chameneoses[c][1] # Faded
          /\ Meet(c)
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

RECURSIVE SumSet(_)
SumSet(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN chameneoses[x][2] + SumSet(S \ {x})

SumMet == numMeetings = N => SumSet(ChameneosID) = 2 * N

AtMostOneWaiting ==
    meetingPlace # MeetingPlaceEmpty => meetingPlace \in ChameneosID

CounterMonotone == [][numMeetings' >= numMeetings]_vars

CounterIncOnlyOnMeeting ==
    [][numMeetings' # numMeetings =>
         /\ numMeetings' = numMeetings + 1
         /\ meetingPlace # MeetingPlaceEmpty
         /\ meetingPlace' = MeetingPlaceEmpty]_vars

BudgetRespected == numMeetings <= N

Termination == <>[](AllFaded)

=============================================================================