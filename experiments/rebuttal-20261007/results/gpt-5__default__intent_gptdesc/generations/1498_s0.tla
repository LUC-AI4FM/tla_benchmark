------------------------------ MODULE ToggleSystem ------------------------------

EXTENDS TLC

CONSTANTS Dummy

VARIABLES b

Init == b = FALSE

ToggleA == b' = ~b

ToggleB == b' = ~b

Next == ToggleA \/ ToggleB

Spec == Init /\ []Next /\ WF_b(ToggleA) /\ WF_b(ToggleB)

TypeInv == b \in BOOLEAN

Flip == b' = ~b

AlwaysBoolean == []TypeInv

AlwaysFlips == []Flip

NeverStuck == [](ENABLED Next)

Alternation == []Flip

NoFixedPoint == []<>(b = TRUE) /\ []<>(b = FALSE)

===============================================================================