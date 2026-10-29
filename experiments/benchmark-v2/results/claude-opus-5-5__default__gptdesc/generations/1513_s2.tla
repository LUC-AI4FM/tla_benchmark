---------------------------- MODULE EWD840_TypeStates ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES active, color, tpos, tcolor

vars == << active, color, tpos, tcolor >>

-----------------------------------------------------------------------------
(* Type constraints over the node set and the two-color domain              *)
-----------------------------------------------------------------------------
TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ color  \in [Node -> Color]
    /\ tpos   \in Node
    /\ tcolor \in Color

-----------------------------------------------------------------------------
(* Constraints restricting the states that may be chosen                    *)
-----------------------------------------------------------------------------
StateConstraint ==
    \/ \A i \in Node : (tpos < i) => ~ active[i]
    \/ \E j \in 0 .. tpos : color[j] = "black"
    \/ tcolor = "black"

-----------------------------------------------------------------------------
(* Initial states: chosen nondeterministically subject to the constraints   *)
-----------------------------------------------------------------------------
Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ color  \in [Node -> Color]
    /\ tpos   \in Node
    /\ tcolor \in Color
    /\ StateConstraint

-----------------------------------------------------------------------------
(* Next-state relation: successor chosen nondeterministically subject to   *)
(* the same constraints                                                     *)
-----------------------------------------------------------------------------
Next ==
    /\ active' \in [Node -> BOOLEAN]
    /\ color'  \in [Node -> Color]
    /\ tpos'   \in Node
    /\ tcolor' \in Color
    /\ StateConstraint'

-----------------------------------------------------------------------------
(* Behavior specification (no fairness conditions)                          *)
-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariant                                                          *)
-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK

=============================================================================