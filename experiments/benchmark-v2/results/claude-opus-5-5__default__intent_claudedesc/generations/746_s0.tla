------------------------------ MODULE Chameneos ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N,   \* total number of meetings that may take place
          M    \* number of chameneos creatures

ASSUME NAssump == N \in Nat \ {0}
ASSUME MAssump == M \in Nat \ {0}

VARIABLES chameneoses,   \* creature id -> << color, personal meeting count >>
          meetingPlace,  \* id of the waiting creature, or MeetingPlaceEmpty
          numMeetings    \* total number of pairwise meetings so far

vars == << chameneoses, meetingPlace, numMeetings >>

-----------------------------------------------------------------------------

ChameneosID == 1..M

LiveColor == {"blue", "red", "yellow"}
Color     == LiveColor \cup {"faded"}

MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* Complement color of a pair: the third color if they differ, else unchanged
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in LiveColor \ {c1, c2} : TRUE

\* Sum of the personal meeting counts of all creatures
RECURSIVE SumCounts(_)
SumCounts(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN  chameneoses[x][2] + SumCounts(S \ {x})

-----------------------------------------------------------------------------

TypeOK ==
    /\ chameneoses \in [ChameneosID -> Color \X (0..N)]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in 0..N

Init ==
    /\ chameneoses \in [ChameneosID -> LiveColor \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

\* Creature cid arrives at the mall
Meet(cid) ==
    /\ chameneoses[cid][1] # "faded"
    /\ cid # meetingPlace
    /\ IF meetingPlace = MeetingPlaceEmpty
         THEN IF numMeetings < N
                \* mall empty and meetings remain: wait
                THEN /\ meetingPlace' = cid
                     /\ UNCHANGED << chameneoses, numMeetings >>
                \* all N meetings done: fade permanently
                ELSE /\ chameneoses' =
                          [chameneoses EXCEPT ![cid] = << "faded", @[2] >>]
                     /\ UNCHANGED << meetingPlace, numMeetings >>
         \* another creature is waiting: the two meet
         ELSE LET other == meetingPlace
                  newColor == Complement(chameneoses[cid][1],
                                         chameneoses[other][1])
              IN  /\ chameneoses' =
                       [chameneoses EXCEPT
                          ![cid]   = << newColor, @[2] + 1 >>,
                          ![other] = << newColor, @[2] + 1 >>]
                  /\ meetingPlace' = MeetingPlaceEmpty
                  /\ numMeetings' = numMeetings + 1

Next == \E cid \in ChameneosID : Meet(cid)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

\* Safety: once exactly N meetings have occurred, the personal counts sum to 2N
SumMeetings ==
    (numMeetings = N) => (SumCounts(ChameneosID) = 2 * N)

\* Liveness: the system eventually terminates with all creatures faded
AllFaded == \A cid \in ChameneosID : chameneoses[cid][1] = "faded"

Termination == <>AllFaded

THEOREM Spec => [](TypeOK /\ SumMeetings)
=============================================================================