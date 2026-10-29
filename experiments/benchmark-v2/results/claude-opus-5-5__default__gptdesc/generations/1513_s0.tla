------------------------------- MODULE EWD840Constrained -------------------------------
EXTENDS Naturals

N == 3
Node == 0 .. N-1
Color == {"white", "black"}

VARIABLES active, color, tpos, tcolor

vars == << active, color, tpos, tcolor >>

-----------------------------------------------------------------------------------------
TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tpos \in Node
  /\ tcolor \in Color

-----------------------------------------------------------------------------------------
(* Initial state: chosen nondeterministically subject to constraints. *)
Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tpos \in Node
  /\ tcolor \in Color
  /\ tpos = 0
  /\ tcolor = "black"

-----------------------------------------------------------------------------------------
(* Next state: successor chosen nondeterministically subject to constraints. *)

InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' \in Node
  /\ tpos' = N-1
  /\ tcolor' \in Color
  /\ tcolor' = "white"
  /\ color' \in [Node -> Color]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ active' = active

PassToken(i) ==
  /\ tpos = i
  /\ i # 0
  /\ ~active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' \in Node
  /\ tpos' = i - 1
  /\ tcolor' \in Color
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ color' \in [Node -> Color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ active' = active

SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Node \ {i} :
       /\ active' \in [Node -> BOOLEAN]
       /\ active' = [active EXCEPT ![j] = TRUE]
       /\ color' \in [Node -> Color]
       /\ color' = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
  /\ UNCHANGED << tpos, tcolor >>

Deactivate(i) ==
  /\ active[i]
  /\ active' \in [Node -> BOOLEAN]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED << color, tpos, tcolor >>

Next ==
  \/ InitiateProbe
  \/ \E i \in Node : PassToken(i)
  \/ \E i \in Node : SendMsg(i)
  \/ \E i \in Node : Deactivate(i)

-----------------------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------------
(* Safety invariant *)
THEOREM TypeCorrect == Spec => []TypeOK

=========================================================================================