------------------------------ MODULE HourClock2 ------------------------------

EXTENDS HourClock, Integers

HCnxt2 ==
  hr' = (hr % 12) + 1

HC2 ==
  HCini /\ [][HCnxt2]_hr

THEOREM HC <=> HC2

=============================================================================