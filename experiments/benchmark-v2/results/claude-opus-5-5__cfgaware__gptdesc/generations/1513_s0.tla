---- MODULE EWD840Abstract ----
EXTENDS Naturals

N == 3
Nodes == 0 .. N-1
Color == {"white", "black"}

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor \in Color

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor = "black"

TypeOKPrime ==
  /\ active' \in [Nodes -> BOOLEAN]
  /\ color' \in [Nodes -> Color]
  /\ tpos' \in Nodes
  /\ tcolor' \in Color

Next ==
  /\ TypeOKPrime
  /\ \/ tpos' = tpos
     \/ tpos' = (tpos + N - 1) % N
     \/ tpos' = N - 1
  /\ \A i \in Nodes : active'[i] => (active[i] \/ \E j \in Nodes : active[j])

Spec == Init /\ [][Next]_vars

====