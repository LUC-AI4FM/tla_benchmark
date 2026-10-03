------------------------------- MODULE SmallStateMachine -------------------------------

CONSTANTS x

VARIABLES state

(*--algorithm SmallStateMachine
variables state = 0;

next == \/ /\ state = 0
             /\ state' = 1
         \/ /\ state = 1
             /\ state' = 2
         \/ /\ state = 2
             /\ state' = 0

Init == state = 0

StateIsOne == state = 1
WorkDone == state = 2
WrapAround == state = 2 /\ state' = 0

Spec ==
    Init /\ [][Next]_<<state>>

Next ==
    \/ /\ StateIsOne
       /\ state' = state
    \/ /\ WorkDone
       /\ state' = state
    \/ next

====