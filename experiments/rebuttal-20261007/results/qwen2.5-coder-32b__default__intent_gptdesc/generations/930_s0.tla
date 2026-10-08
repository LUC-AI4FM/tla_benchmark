------------------------------- MODULE Clock -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS HourSet

VARIABLES hour

HourSet == {1..12}

Init == hour \in HourSet

Next ==
  \/ /\ hour' = (hour % 12) + 1
     /\ hour' \in HourSet

Spec ==
  /\ Init
  /\ [][Next]_<<hour>>
  /\ WF_next(<<hour>>)

InvHourRange == hour \in HourSet
InvModuloIncrement == hour' = (hour % 12) + 1

TypeOK == InvHourRange

TemporalProperties ==
  /\ []TypeOK
  /\ [](TypeOK => ['][TypeOK]_<<hour>>)
  /\ <>(/\ hour = 1
         /\ <>[]<>(hour = 2)
         /\ <>[]<>(hour = 3)
         /\ <>[]<>(hour = 4)
         /\ <>[]<>(hour = 5)
         /\ <>[]<>(hour = 6)
         /\ <>[]<>(hour = 7)
         /\ <>[]<>(hour = 8)
         /\ <>[]<>(hour = 9)
         /\ <>[]<>(hour = 10)
         /\ <>[]<>(hour = 11)
         /\ <>[]<>(hour = 12))

=============================================================================