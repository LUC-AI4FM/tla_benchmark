----------------------------- MODULE Chameneos -----------------------------

EXTENDS Naturals

CONSTANTS N, M

(*
  Basic sets and symbols
*)
BaseColors == {"blue", "red", "yellow"}
Faded == "Faded"
Colors == BaseColors \cup {Faded}
None == "none"
IDs == 1..M

(*
  State variables:
    chameneoses: function from each ID to a record [color, cnt]
    meetingPlace: which single creature (if any) is currently waiting
    numMeetings: global number of completed meetings
*)
VARIABLES chameneoses, meetingPlace, numMeetings

vars == << chameneoses, meetingPlace, numMeetings >>

(*
  Helper predicates and operators
*)
NonFaded(i) == chameneoses[i].color # Faded

Complement(c1, c2) ==
  IF c1 = c2
    THEN c1
    ELSE CHOOSE c \in BaseColors : c # c1 /\ c # c2

RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {}
    THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN SumOver(S \ {x}) + chameneoses[x].cnt

SumCnt == SumOver(IDs)

(*
  Typing and basic well-formedness invariant (for checking)
*)
TypeInv ==
  /\ chameneoses \in [IDs -> [color: Colors, cnt: Nat]]
  /\ meetingPlace \in ({None} \cup IDs)
  /\ numMeetings \in Nat

(*
  Initialization:
    - Each chameneos starts non-faded with a base color and cnt = 0
    - Meeting place is empty
    - Global meeting count is 0
*)
Init ==
  /\ chameneoses \in [IDs -> [color: BaseColors, cnt: 0]]
  /\ meetingPlace = None
  /\ numMeetings = 0

(*
  Actions for a single chameneos i
*)
ChamEnter(i) ==
  /\ NonFaded(i)
  /\ meetingPlace = None
  /\ numMeetings < N
  /\ meetingPlace' = i
  /\ chameneoses' = chameneoses
  /\ numMeetings' = numMeetings

ChamFade(i) ==
  /\ NonFaded(i)
  /\ meetingPlace = None
  /\ numMeetings = N
  /\ chameneoses' = [chameneoses EXCEPT ![i].color = Faded]
  /\ meetingPlace' = meetingPlace
  /\ numMeetings' = numMeetings

ChamMeet(i) ==
  /\ NonFaded(i)
  /\ meetingPlace \in IDs
  /\ meetingPlace # i
  /\ numMeetings < N
  /\ LET j == meetingPlace IN
     /\ NonFaded(j)
     /\ LET newC == Complement(chameneoses[i].color, chameneoses[j].color) IN
        /\ chameneoses' =
             [ chameneoses EXCEPT
               ![i].color = newC,
               ![j].color = newC,
               ![i].cnt = @ + 1,
               ![j].cnt = @ + 1
             ]
        /\ meetingPlace' = None
        /\ numMeetings' = numMeetings + 1

ChamAct(i) == ChamEnter(i) \/ ChamFade(i) \/ ChamMeet(i)

(*
  Next-state relation: at least one non-faded chameneos acts
*)
Next ==
  \E i \in IDs : NonFaded(i) /\ ChamAct(i)

(*
  The main behavior spec: no additional fairness conditions
*)
Spec == Init /\ [][Next]_vars

(*
  Safety property:
    Once numMeetings reaches N, the sum of all individual meeting counts equals 2*N.
*)
SumMet == (numMeetings # N) \/ (SumCnt = 2 * N)

============================================================================