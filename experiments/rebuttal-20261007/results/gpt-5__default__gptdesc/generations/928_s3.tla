----------------------------- MODULE HC2 -----------------------------
EXTENDS HourClock, Integers

CONSTANTS Dummy

VARIABLES hr

HCnxt2 ==
  hr' = (hr % 12) + 1

Init ==
  HCini

Next ==
  HCnxt2

Spec ==
  Init /\ [] [Next]_hr

HC2 ==
  HCini /\ [] [HCnxt2]_hr

THEOREM HC = HC2
======================================================================