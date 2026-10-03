----------------------------- MODULE HC2 -----------------------------

EXTENDS Naturals

CONSTANTS DUMMY

VARIABLES hr

HCX == INSTANCE HourClock WITH hr <- hr

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCX!HCini /\ [][HCnxt2]_hr

Init == HCX!HCini

Next == HCnxt2

Spec == HC2

THEOREM HCX!HC <=> HC2

======================================================================