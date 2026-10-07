------------------------------ MODULE Chameneos ------------------------------

EXTENDS Naturals

CONSTANTS
  Chameneos, \* Nonempty finite set of chameneos identifiers
  N          \* Global meeting limit

ASSUME
  /\ Chameneos # {}
  /\ N \in Nat

Colors == 1..3

Complement(c1, c2) ==
  IF c1 = c2 THEN c1 ELSE 6 - c1 - c2

VARIABLES
  color,      \* [Chameneos -> Colors]
  meetCount,  \* [Chameneos -> Nat]
  place,      \* {} or {p} for some p \in Chameneos
  total,      \* Nat, number of completed meetings
  faded       \* [Chameneos -> BOOLEAN]

vars == << color, meetCount, place, total, faded >>

PlaceType == { {} } \cup { {p} : p \in Chameneos }

Init ==
  /\ color \in [Chameneos -> Colors]
  /\ meetCount = [c \in Chameneos |-> 0]
  /\ place = {}
  /\ total = 0
  /\ faded = [c \in Chameneos |-> FALSE]

Arrive(c) ==
  /\ c \in Chameneos
  /\ ~faded[c]
  /\ total < N
  /\ place = {}
  /\ place' = {c}
  /\ UNCHANGED << color, meetCount, total, faded >>

Meet(c) ==
  \E d \in Chameneos:
    /\ d # c
    /\ place = {d}
    /\ total < N
    /\ ~faded[c] /\ ~faded[d]
    /\ LET newCol == Complement(color[c], color[d]) IN
         /\ color' = [color EXCEPT ![c] = newCol, ![d] = newCol]
         /\ meetCount' = [meetCount EXCEPT ![c] = @ + 1, ![d] = @ + 1]
    /\ total' = total + 1
    /\ place' = {}
    /\ faded' = faded

FadeArrive(c) ==
  /\ c \in Chameneos
  /\ ~faded[c]
  /\ total >= N
  /\ place = {}
  /\ faded' = [faded EXCEPT ![c] = TRUE]
  /\ UNCHANGED << color, meetCount, total, place >>

FadeAtBusy(c) ==
  /\ c \in Chameneos
  /\ ~faded[c]
  /\ total >= N
  /\ place # {}
  /\ c \notin place
  /\ faded' = [faded EXCEPT ![c] = TRUE]
  /\ UNCHANGED << color, meetCount, total, place >>

FadeWaiting(c) ==
  /\ c \in Chameneos
  /\ ~faded[c]
  /\ total >= N
  /\ place = {c}
  /\ place' = {}
  /\ faded' = [faded EXCEPT ![c] = TRUE]
  /\ UNCHANGED << color, meetCount, total >>

Next ==
  \E c \in Chameneos:
       Arrive(c)
    \/ Meet(c)
    \/ FadeArrive(c)
    \/ FadeAtBusy(c)
    \/ FadeWaiting(c)

RECURSIVE SumMeetCounts(_)
SumMeetCounts(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S: TRUE
       IN meetCount[x] + SumMeetCounts(S \ {x})

SumCounts == SumMeetCounts(Chameneos)

TypeInv ==
  /\ color \in [Chameneos -> Colors]
  /\ meetCount \in [Chameneos -> Nat]
  /\ place \in PlaceType
  /\ total \in Nat /\ total <= N
  /\ faded \in [Chameneos -> BOOLEAN]

ArithSafety ==
  (total = N) => (SumCounts = 2 * N)

Spec == Init /\ [][Next]_vars

=============================================================================