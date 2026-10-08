----------------------------- MODULE HourClock -----------------------------
EXTENDS Integers

CONSTANT N
ASSUME N = 12

VARIABLES hour

Hours == 1..N

NextHour(h) == IF h < N THEN h + 1 ELSE 1

Init == hour \in Hours

Advance == hour' = NextHour(hour)

Next == Advance

vars == << hour >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*
  Safety invariants
*)
TypeInv == hour \in Hours

StepOK == (hour' = hour) \/ (hour' = NextHour(hour))

(*
  Theorems/properties implied by Spec
*)
THEOREM SpecTypeInvariant ==
  Spec => []TypeInv

THEOREM StepSafety ==
  Spec => [](StepOK)

THEOREM AlwaysEnabledAdvance ==
  Spec => [](Enabled Advance)

THEOREM InfinitelyManyAdvances ==
  Spec => []<>(hour = 1)

THEOREM EveryHourOccursInfOften ==
  Spec => ∀ v \in Hours: []<>(hour = v)
============================================================================