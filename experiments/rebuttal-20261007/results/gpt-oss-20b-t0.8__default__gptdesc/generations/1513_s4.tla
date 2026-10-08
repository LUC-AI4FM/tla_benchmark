--------------------------- MODULE SimpleStateMachine ---------------------------
EXTENDS SETS

CONSTANTS NodeSet, ColorSet

VARIABLES ActivityStatus, NodeColors, TokenPos, TokenColor

Vars == <<ActivityStatus, NodeColors, TokenPos, TokenColor>>

TypeInv ==
  /\ ActivityStatus \in [NodeSet -> BOOLEAN]
  /\ NodeColors \in [NodeSet -> ColorSet]
  /\ TokenPos \in NodeSet
  /\ TokenColor \in ColorSet

Init ==
  TypeInv

Next ==
  /\ ActivityStatus' \in [NodeSet -> BOOLEAN]
  /\ NodeColors' \in [NodeSet -> ColorSet]
  /\ TokenPos' \in NodeSet
  /\ TokenColor' \in ColorSet

Spec == Init /\ [] Next /\ [] TypeInv

=============================================================================