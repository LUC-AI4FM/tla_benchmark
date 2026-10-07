--------------------------- MODULE HourClock ---------------------------

EXTENDS Integers

CONSTANTS MinHr, MaxHr

ASSUME MinHr = 1 /\ MaxHr = 12

VARIABLES hr

HCini == hr \in MinHr..MaxHr

HCnxt == hr' = IF hr # MaxHr THEN hr + 1 ELSE MinHr

Init == HCini

Next == HCnxt

HC == Init /\ []Next

Spec == HC

THEOREM HC => []HCini

=============================================================================