MODULE SimpleClock
EXTENDS Naturals

VARIABLES hr

HCini == 1 <= hr /\ hr <= 12
HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Init == HCini
Next == HCnxt
Spec == Init /\ [] Next

THEOREM ClockInvariant : Spec => [] HCini

===============================================================================