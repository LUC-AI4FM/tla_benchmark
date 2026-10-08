MODULE IncrementStutter
EXTENDS Naturals

VARIABLES x

Init == x = 0

Inc == x' = x + 1 /\ x < 3

Stutter == x' = x

Next == Inc \/ Stutter

Safety == [] (x <= 3)

Spec == Init /\ [] Next /\ Safety

===============================================================================