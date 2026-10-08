------------------------------- MODULE ClockEquivalence -------------------------------
EXTENDS HourClock

CONSTANTS InitHour \* Assuming HourClock defines an initial hour constant or variable

VARIABLES hour

Init == hour = InitHour

Next ==
    \/ /\ hour < 12
       /\ hour' = hour + 1
    \/ /\ hour = 12
       /\ hour' = 1

ModularNext ==
    hour' = (hour % 12) + 1

Spec ==
    /\ Init
    /\ [][Next]_<<hour>>
    /\ [][ModularNext]_<<hour>>

THEOREM Spec => [](Next <=> ModularNext)

=============================================================================