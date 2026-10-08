------------------------------- MODULE SimpleClock -------------------------------
EXTENDS Naturals, TLC

CONSTANTS InitHour \* The initial hour can be any value between 1 and 12

VARIABLES hour

Init == /\ hour = InitHour
        /\ 1 <= hour /\ hour <= 12

Next == \/ hour' = IF hour < 12 THEN hour + 1 ELSE 1
        \/ hour' = hour \* Stuttering step

Spec == /\ Init
        /\ [][Next]_<<hour>>

\* Invariants
ValidHour == 1 <= hour /\ hour <= 12

\* Liveness properties (none specified in the description)

\* Fairness conditions (none specified in the description)

=============================================================================