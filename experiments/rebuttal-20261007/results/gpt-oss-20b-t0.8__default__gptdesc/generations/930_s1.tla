```
MODULE Clock12
EXTENDS Naturals

VARIABLES hr

HCini == hr \in 1..12

HCnxt ==
    \/ (hr = 12 /\ hr' = 1)
    \/ ((hr \in 1..11) /\ hr' = hr + 1)

Init == HCini

Next == HCnxt

Spec == Init /\ [][Next]_hr

THEOREM InvariantHCI : [] HCini
```