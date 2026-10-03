----------------------------- MODULE Chameneos -----------------------------
EXTENDS Naturals

CONSTANTS
  C, \* Set of chameneoses (agents)
  N, \* Total meeting limit
  R, G, B, \* Three distinct colors
  Null \* Distinct "empty" marker for the meeting place

ASSUME R # G /\ R # B /\ G # B
ASSUME Null \notin C
ASSUME N \in Nat

Colors == {R, G, B}

Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in Colors: c # c1 /\ c # c2

VARIABLES
  color,        \* [C -> Colors], current color of each chameneos
  count,        \* [C -> Nat], individual meeting counters
  totalCounts,  \* Nat, total of all individual counters (maintained incrementally)
  slot,         \* either Null or an element of C (waiting chameneos)
  meetings,     \* Nat, total number of completed meetings
  faded         \* subset of C, chameneoses that faded after closure

vars == << color, count, totalCounts, slot, meetings, faded >>

IsActive(i) == i \in C /\ i \notin faded

Init ==
  /\ color \in [C -> Colors]
  /\ count = [i \in C |-> 0]
  /\ totalCounts = 0
  /\ slot = Null
  /\ meetings = 0
  /\ faded = {}

EnterAction ==
  \E i \in C:
    /\ IsActive(i)
    /\ meetings < N
    /\ slot = Null
    /\ slot' = i
    /\ UNCHANGED << color, count, totalCounts, meetings, faded >>

MeetAction ==
  \E i, j \in C:
    /\ i # j
    /\ IsActive(i) /\ IsActive(j)
    /\ meetings < N
    /\ slot = i
    LET new == Complement(color[i], color[j]) IN
      /\ color' = [color EXCEPT ![i] = new, ![j] = new]
      /\ count' = [count EXCEPT ![i] = @ + 1, ![j] = @ + 1]
      /\ totalCounts' = totalCounts + 2
      /\ meetings' = meetings + 1
      /\ slot' = Null
      /\ UNCHANGED faded

FadeAction ==
  \E k \in C:
    /\ meetings = N
    /\ IsActive(k)
    /\ faded' = faded \cup {k}
    /\ UNCHANGED << color, count, totalCounts, meetings, slot >>

Next ==
  \/ EnterAction
  \/ MeetAction
  \/ FadeAction

Spec == Init /\ [][Next]_vars

(*
  Safety invariants
*)
TypeInv ==
  /\ color \in [C -> Colors]
  /\ count \in [C -> Nat]
  /\ totalCounts \in Nat
  /\ slot \in C \cup {Null}
  /\ meetings \in Nat
  /\ meetings <= N
  /\ faded \subseteq C

ArithAtLimit ==
  meetings = N => totalCounts = 2 * N
=============================================================================