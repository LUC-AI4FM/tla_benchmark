---------------------------- MODULE SimpleStateMachine ----------------------------
EXTENDS Naturals

CONSTANTS NodeSet, Red, Green

VARIABLES active, color, tokenPos, tokenColor

ColorSet == {Red, Green}

vars == {active, color, tokenPos, tokenColor}

TypeInv ==
    /\ active \in [NodeSet -> BOOLEAN]
    /\ color  \in [NodeSet -> ColorSet]
    /\ tokenPos \in NodeSet
    /\ tokenColor \in ColorSet

Init == TypeInv

Next ==
    /\ active' \in [NodeSet -> BOOLEAN]
    /\ color'  \in [NodeSet -> ColorSet]
    /\ tokenPos'\in NodeSet
    /\ tokenColor' \in ColorSet

Spec == Init /\ [][Next]_vars
=============================================================================