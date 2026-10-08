```tla
MODULE HourClockExtended

EXTENDS Naturals, TLC, Integers

CONSTANTS HrInit

VARIABLES hr

HC == /\ TYPEOK(hr)
      /\ 1 <= hr /\ hr <= 12

HCnxt == \/ /\ hr < 12 
               /\ hr' = hr + 1
          \/ /\ hr = 12 
               /\ hr' = 1

Init == HC /\ hr = HrInit

Next == HC /\ HCnxt

Spec ==
  Init /\ [][Next]_<<hr>> /\ WF_hr(Next)

WF_HR_Tick ==
  \A h \in 1..12: [](<>[][hr = h]_<<hr>>)

THEOREM Spec => []HC /\ <>[]Next /\ WF_HR_Tick

=============================================================================
```