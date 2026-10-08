---------------------------- MODULE ToggleSystem ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Actions
VARIABLE state

Init == (state = FALSE)

Next == (state' = IF Action = "toggle1" THEN ~state ELSE ~state)

Spec == Init /\ [][Next]_state

THEOREM Spec => []<>(state = TRUE)
THEOREM Spec => []<>(state = FALSE)
THEOREM Spec => [](state \in {TRUE, FALSE})
THEOREM Spec => <><<Action = "toggle1">>_
THEOREM Spec => <><<Action = "toggle2">>_

=============================================================================