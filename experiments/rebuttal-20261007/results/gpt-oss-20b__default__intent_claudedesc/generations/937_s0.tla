------------------------------ MODULE HourClock ------------------------------
EXTENDS Naturals

VARIABLE hour

Init == hour = 1

Tick == hour' = IF hour = 12 THEN 1 ELSE hour + 1

Next == Tick

State == hour \in 1..12
-----------------------------------------------------------------

------------------------------ MODULE LiveHourClock ------------------------------
EXTENDS HourClock, TemporalOperators

vars == <<hour>>

Spec == Init /\ [][Next]_vars /\ WF_0(Tick)

Theorem LiveSpecImpliesProps ==
    Spec => ( WF_0(Tick) /\
              []<>(hour = 1) /\ []<>(hour = 2) /\ []<>(hour = 3) /\ []<>(hour = 4) /\ []<>(hour = 5) /\ []<>(hour = 6) /\ []<>(hour = 7) /\ []<>(hour = 8) /\ []<>(hour = 9) /\ []<>(hour = 10) /\ []<>(hour = 11) /\ []<>(hour = 12) /\
              hour \in 1..12 )
-----------------------------------------------------------------