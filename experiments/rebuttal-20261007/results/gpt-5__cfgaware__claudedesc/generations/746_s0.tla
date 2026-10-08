----------------------------- MODULE Chameneos -----------------------------
EXTENDS Naturals

CONSTANTS N, M

VARIABLES chameneoses, meetingPlace, numMeetings

ColorSet == {"blue", "red", "yellow"}
Faded == "Faded"
None == "None"
CHColors == ColorSet \cup {Faded}
Creatures == 1..M

Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in ColorSet : c # c1 /\ c # c2

Init ==
  /\ N \in Nat
  /\ M \in Nat \ {0}
  /\ chameneoses \in [Creatures -> [color : ColorSet, count : {0}]]
  /\ meetingPlace = None
  /\ numMeetings = 0

Meet(c) ==
  /\ c \in Creatures
  /\ chameneoses[c].color # Faded
  /\ IF meetingPlace = None THEN
        IF numMeetings < N THEN
          /\ meetingPlace' = c
          /\ UNCHANGED << chameneoses, numMeetings >>
        ELSE
          /\ chameneoses' = [chameneoses EXCEPT ![c].color = Faded]
          /\ UNCHANGED << meetingPlace, numMeetings >>
     ELSE
        LET w == meetingPlace IN
          /\ w \in Creatures
          /\ w # c
          /\ chameneoses[w].color # Faded
          /\ numMeetings < N
          /\ LET newCol == Complement(chameneoses[c].color, chameneoses[w].color) IN
               /\ chameneoses' =
                    [chameneoses EXCEPT
                      ![c].color = newCol,
                      ![c].count = @ + 1,
                      ![w].color = newCol,
                      ![w].count = @ + 1]
               /\ meetingPlace' = None
               /\ numMeetings' = numMeetings + 1

Next ==
  \E c \in Creatures : Meet(c)

vars == << chameneoses, meetingPlace, numMeetings >>

RECURSIVE SumFrom(_)
SumFrom(i) ==
  IF i = 0 THEN 0
  ELSE chameneoses[i].count + SumFrom(i - 1)

SumCounts == SumFrom(M)

TypeOK ==
  /\ N \in Nat
  /\ M \in Nat \ {0}
  /\ chameneoses \in [Creatures -> [color : CHColors, count : Nat]]
  /\ meetingPlace \in Creatures \cup {None}
  /\ numMeetings \in 0..N

SumMet ==
  (numMeetings < N) \/ (SumCounts = 2 * N)

Spec == Init /\ [][Next]_vars

============================================================================