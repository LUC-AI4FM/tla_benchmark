---------------------------- MODULE EWD998Random ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0} /\ N <= 4

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES active, color, tpos, tcolor

vars == << active, color, tpos, tcolor >>

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ color  \in [Node -> Color]
    /\ tpos   \in Node
    /\ tcolor \in Color

-----------------------------------------------------------------------------

(* Initial states are chosen nondeterministically from the type,          *)
(* subject to the constraint that the token starts at the initiator        *)
(* (node 0) and is black, as in the EWD998 algorithm.                      *)
Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ color  \in [Node -> Color]
    /\ tpos   = 0
    /\ tcolor = "black"

(* The successor state is chosen nondeterministically from the type,      *)
(* subject to the constraints that the token either stays where it is or   *)
(* moves one step towards the initiator (wrapping around from 0 to N-1),   *)
(* and that the state actually changes.                                    *)
Next ==
    /\ active' \in [Node -> BOOLEAN]
    /\ color'  \in [Node -> Color]
    /\ tpos'   \in Node
    /\ tcolor' \in Color
    /\ \/ tpos' = tpos
       \/ tpos # 0 /\ tpos' = tpos - 1
       \/ tpos = 0 /\ tpos' = N - 1
    /\ vars' # vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

THEOREM Spec => []TypeOK

=============================================================================