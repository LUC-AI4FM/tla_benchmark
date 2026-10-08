----------------------------- MODULE ToggleSystem -----------------------------

EXTENDS TLC

CONSTANTS Dummy \* Unused placeholder to satisfy CONSTANTS requirement

VARIABLES b

Flip(v) == ~v

Init == b = FALSE

ActionA == b' = Flip(b)

ActionB == b' = Flip(b)

Next == ActionA \/ ActionB

Spec == Init /\ [][Next]_b

==============================================================================