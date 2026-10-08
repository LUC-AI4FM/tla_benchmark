------------------------------- MODULE HourClock -------------------------------
EXTENDS Naturals, TLC

CONSTANTS 
    \* No constants needed for this simple model

VARIABLES 
    hour

Init == hour = 1

Next ==
    \/ /\ hour \in 1..12
       /\ hour' = IF hour < 12 THEN hour + 1 ELSE 1

Spec ==
    /\ Init
    /\ [][Next]_<<hour>>
    /\ WF_next(<<hour>>)

InvHourBounds == hour \in 1..12

InvAdvancingSteps ==
    [](hour # hour' => hour' = IF hour < 12 THEN hour + 1 ELSE 1)

InvAllHoursInfinitelyOften ==
    \A h \in 1..12: <>[] (hour = h)

THEOREM Spec => []InvHourBounds
THEOREM Spec => InvAdvancingSteps
THEOREM Spec => InvAllHoursInfinitelyOften

=============================================================================