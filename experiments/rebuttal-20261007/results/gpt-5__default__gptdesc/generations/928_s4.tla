------------------------------ MODULE HC2 ------------------------------

EXTENDS Integers

CONSTANTS DUMMY

VARIABLES hr

HCInst == INSTANCE HourClock WITH hr <- hr

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCInst!HCini /\ [][HCnxt2]_hr

Init == HCInst!HCini
Next == HCnxt2
Spec == HC2

THEOREM HC_Equivalence == HCInst!HC = HC2

=============================================================================