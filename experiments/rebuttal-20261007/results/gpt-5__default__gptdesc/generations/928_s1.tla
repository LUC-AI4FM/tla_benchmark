----------------------------- MODULE HC2 -----------------------------
EXTENDS HourClock, Integers

CONSTANTS DummyConst
VARIABLES DummyVar

HCnxt2 ==
  hr' = (hr % 12) + 1

HC2 ==
  HCini /\ [] [HCnxt2]_hr

Init == HCini
Next == HCnxt2
Spec == HC2

THEOREM HC <=> HC2

=============================================================================