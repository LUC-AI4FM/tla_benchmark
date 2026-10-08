---- MODULE TemporalTautologyDemo ----

EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

AlwaysTrue == <>TRUE => <>[]TRUE

THEOREM AlwaysTrueIsTautology == AlwaysTrue
PROOF
  BY PTL
QED

THEOREM SpecImpliesAlwaysTrue == Spec => AlwaysTrue
PROOF
  BY PTL DEF Spec, Init, Next, AlwaysTrue
QED

====