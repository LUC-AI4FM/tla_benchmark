```
MODULE ToggleSystem
EXTENDS Integers, Bool

CONSTANTS None

VARIABLES state, action

Init == (state = FALSE) /\ (action = "none")

Next == (action = "toggle1") /\ (state' = ~state)
       \/ (action = "toggle2") /\ (state' = ~state)

Spec == Init /\ [][Next]_<<state, action>>

Fairness == WF_action("toggle1") /\ WF_action("toggle2")

StateInvariant == state \in {TRUE, FALSE}

TransitionInvariant == (state' = ~state)

Liveness == []<>~(state = TRUE) /\ []<>~(state = FALSE)

THEOREM Spec => []StateInvariant
THEOREM Spec => [][TransitionInvariant]_state
THEOREM Spec => Liveness
THEOREM Spec => Fairness
```