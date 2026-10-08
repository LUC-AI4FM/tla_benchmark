------------------------------ MODULE ToggleSystem ------------------------------
EXTENDS Naturals, TLC

VARIABLES state

Init == state = FALSE

Toggle1 == state' = ~state
Toggle2 == state' = ~state

Next == Toggle1 \/ Toggle2

Spec == Init /\ [][Next]_<<state>> /\ Fairness(Toggle1) /\ Fairness(Toggle2)

StateIsBool == [] (state ∈ {TRUE, FALSE})
NoStuckInvariant == [] (Toggle1 \/ Toggle2)
Liveness == []<>(state = TRUE) /\ []<>(state = FALSE)

=============================================================================