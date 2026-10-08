---- MODULE ToggleSystem ----

VARIABLES toggleState

(*--algorithm ToggleSystem
variables toggleState \in BOOLEAN;

Init == toggleState = FALSE

Negate(b) == ~b

Next ==
    \/ /\ TRUE
       /\ toggleState' = Negate(toggleState)
    \/ /\ TRUE
       /\ toggleState' = Negate(toggleState)

end algorithm *)
====