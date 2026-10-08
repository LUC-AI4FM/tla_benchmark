------------------------------- MODULE ClockSpecification -------------------------------
EXTENDS Naturals, TLC

CONSTANTS InitHour \* Nondeterministically chosen initial hour

VARIABLES hour

Init == /\ hour = InitHour
        /\ 1 <= hour /\ hour <= 12

Next ==
    \/ /\ hour' = IF hour < 12 THEN hour + 1 ELSE 1
       /\ hour'' = (hour % 12) + 1
          \/ hour'' = 1
    \/ /\ hour'' = IF hour < 12 THEN hour + 1 ELSE 1
       /\ hour' = (hour % 12) + 1
          \/ hour' = 1

Spec ==
    /\ Init
    /\ [][Next]_<<hour>>

InvHourRange == 1 <= hour /\ hour <= 12

InvEquivalence == hour' = hour''

TypeOK == InvHourRange /\ InvEquivalence

TemporalProperties ==
    /\ []<>[](hour' # hour)
    /\ [](hour' = IF hour < 12 THEN hour + 1 ELSE 1)

SpecWithInvariants ==
    /\ Spec
    /\ TypeOK
    /\ TemporalProperties

=============================================================================