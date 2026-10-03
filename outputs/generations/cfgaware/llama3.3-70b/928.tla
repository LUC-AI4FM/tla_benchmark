```
EXTENDS HourClock

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini ∧ [][HCnxt2]_hr

THEOREM HC ≡ HC2
```