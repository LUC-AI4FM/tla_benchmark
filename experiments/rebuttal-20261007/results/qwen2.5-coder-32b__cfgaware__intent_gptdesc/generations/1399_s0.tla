------------------------------- MODULE ToggleSystem -------------------------------

VARIABLE state

CONSTANTS TRUE FALSE

Init == state = TRUE

Next == \/ state' = ~state
        \/ state' = state

Spec == Init /\ [][Next]_<<state>>

Safety == [](state \in {TRUE, FALSE})

Liveness == <>(\/ state' = ~state)

StrongInvariant == [](state = TRUE)

WeakInvariant == <>(state = TRUE) /\ <>(state = FALSE)

Prop == Spec /\ Safety /\ Liveness /\ StrongInvariant /\ WeakInvariant

=============================================================================