---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS Creatures, N

(*
  Colors are the three standard Chameneos colors; strings are atoms in TLA+.
*)
Colors == {"blue", "red", "yellow"}

None == "None"

(*
  State variables:
    col    : current color of each creature
    met    : individual meeting counters per creature
    place  : shared single-slot meeting place (None or a record [who, color])
    total  : total number of meetings that have occurred
    faded  : set of creatures that have faded (after the meeting limit is reached)
*)
VARIABLES col, met, place, total, faded

vars == << col, met, place, total, faded >>

(*
  Type correctness invariant.
*)
TypeOK ==
  /\ col \in [Creatures -> Colors]
  /\ met \in [Creatures -> Nat]
  /\ faded \subseteq Creatures
  /\ (place = None) \/ (place \in [who : Creatures, color : Colors])
  /\ total \in Nat
  /\ N \in Nat

(*
  Symmetric complement color rule:
  If two colors are equal, result is that color; otherwise, the third color.
*)
Comp(c1, c2) ==
  IF c1 = c2
  THEN c1
  ELSE CHOOSE c \in Colors \ {c1, c2} : TRUE

(*
  Initialization:
    - arbitrary initial colors
    - zero individual meeting counters
    - empty meeting place
    - zero total meetings
    - no one has faded
*)
Init ==
  /\ col \in [Creatures -> Colors]
  /\ met = [c \in Creatures |-> 0]
  /\ place = None
  /\ total = 0
  /\ faded = {}

(*
  An unfaded creature i arrives to wait in the empty meeting place, before the limit.
*)
Wait(i) ==
  /\ i \in Creatures
  /\ i \notin faded
  /\ total < N
  /\ place = None
  /\ UNCHANGED << col, met, total, faded >>
  /\ place' = [who |-> i, color |-> col[i]]

(*
  An unfaded creature i meets the currently waiting unfaded creature j (j # i),
  both change colors via Comp, both increment met counters, total increments,
  and the place becomes empty.
*)
Meet(i) ==
  /\ i \in Creatures
  /\ i \notin faded
  /\ total < N
  /\ place \in [who : Creatures, color : Colors]
  /\ place.who # i
  /\ place.who \notin faded
  LET j == place.who IN
  LET new == Comp(col[i], place.color) IN
    /\ col' = [col EXCEPT ![i] = new, ![j] = new]
    /\ met' = [met EXCEPT ![i] = @ + 1, ![j] = @ + 1]
    /\ total' = total + 1
    /\ place' = None
    /\ faded' = faded

(*
  After the global meeting limit N is reached, any unfaded creature that
  takes a step fades instead of attempting to meet. If it is the current
  waiter in the place, it also vacates the place.
*)
Fade(i) ==
  /\ i \in Creatures
  /\ i \notin faded
  /\ total >= N
  /\ col' = col
  /\ met' = met
  /\ total' = total
  /\ faded' = faded \cup {i}
  /\ place' =
       IF place \in [who : Creatures, color : Colors] /\ place.who = i
       THEN None
       ELSE place

Next ==
  \E i \in Creatures :
       Wait(i)
    \/ Meet(i)
    \/ Fade(i)

Spec == Init /\ [][Next]_vars

(*
  Sum of all individual meeting counters.
*)
RECURSIVE SumOver(_, _)
SumOver(F, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN F[x] + SumOver(F, S \ {x})

SumMet == SumOver(met, Creatures)

====