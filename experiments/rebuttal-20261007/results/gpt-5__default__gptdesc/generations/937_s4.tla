--------------------------- MODULE HourClockWithLiveness ---------------------------

EXTENDS Naturals, TLC

CONSTANTS Hours
ASSUME Hours = 1..12

VARIABLES hr

(*
  Basic typing
*)
TypeOK == hr \in Hours

(*
  Canonical first/last hour for the cyclic increment
*)
FirstHour == 1
LastHour  == 12

(*
  HourClock safety: initialization and next-step relation
*)
HCInit == TypeOK

HCnxt ==
  /\ TypeOK
  /\ hr' = IF hr # LastHour THEN hr + 1 ELSE FirstHour

HC == HCInit /\ [][HCnxt]_hr

(*
  Required top-level names
*)
Init == HCInit
Next == HCnxt
Spec == HC

(*
  Augmented liveness: weak fairness on hr for HCnxt
*)
LSpec == HC /\ WF_hr(HCnxt)

(*
  Liveness properties:
   - ticking happens infinitely often
   - every hour value from 1..12 recurs infinitely often
   - the typing condition holds always
*)
Tick == HCnxt
TicksInfOften == []<>(Tick)

HoursInfOften == \A h \in Hours : []<>(hr = h)

AlwaysTypeOK == []TypeOK

(*
  Settling property and a concrete counterexample structure
*)
SettleProp == <>(\E h \in Hours : [](hr = h))
NotSettling == ~SettleProp

CyclicCounterexample ==
  /\ []<>(hr = 1)
  /\ []<>(hr = 2)
  /\ []<>(hr = 3)
  /\ []<>(hr = 4)
  /\ []<>(hr = 5)
  /\ []<>(hr = 6)
  /\ []<>(hr = 7)
  /\ []<>(hr = 8)
  /\ []<>(hr = 9)
  /\ []<>(hr = 10)
  /\ []<>(hr = 11)
  /\ []<>(hr = 12)

Post == CyclicCounterexample

(*
  Theorem: LSpec entails the stated liveness and safety properties,
           and provides a concrete counterexample to settling.
*)
THEOREM FromLSpec ==
  LSpec =>
    /\ TicksInfOften
    /\ HoursInfOften
    /\ AlwaysTypeOK
    /\ NotSettling
    /\ Post

=============================================================================