```
MODULE HC2
EXTENDS HourClock

CONSTANTS None

VARIABLES hr

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini ∧ [][HCnxt2]_hr

Spec == HC2

THEOREM HC ≡ HC2
```