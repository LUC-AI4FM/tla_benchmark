```tla
MODULE HourClockAugmented

EXTENDS Naturals, FiniteSequences, TLC

CONSTANTS HCnxt

VARIABLES hr

Init == (hr = 1)

Next ==
    \/ /\ hr \in 1..12
       /\ hr' = IF hr < 12 THEN hr + 1 ELSE 1
    \/ HCnxt

WF_HCnxt_hr == WF_hr(HCnxt)

Spec ==
    /\ Init
    /\ [][Next]_<<hr>>
    /\ WF_HCnxt_hr

LSpec ==
    Spec
    /\ [](<>HCnxt)
    /\ [](<>(\A h \in 1..12 : hr = h))
    /\ [](Init => []Init)

THEOREM 
    LSpec =>
        [](<>HCnxt) 
        /\ [](<>(\A h \in 1..12 : hr = h)) 
        /\ [](Init => []Init)

POSTCONDITION ==
    <>(hr = 1)
```