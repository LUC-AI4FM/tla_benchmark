------------------------------ MODULE Toggle ------------------------------
EXTENDS Naturals, TLC

VARIABLE state

Init == state = TRUE

Flip    == state' = NOT state
Stutter == state' = state

Next == Flip \/ Stutter

StrongInv          == [](state = TRUE)
ObservationalClaim == [] (state = TRUE \/ state = FALSE)

NoDeadlock == [] <> (∃ state' : (state' = NOT state) \/ (state' = state))

Spec == Init /\ [][Next]_state /\ NoDeadlock /\ ObservationalClaim

=============================================================================