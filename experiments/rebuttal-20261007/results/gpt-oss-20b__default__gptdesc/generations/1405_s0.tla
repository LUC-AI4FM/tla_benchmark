------------------------------ MODULE Inner ------------------------------
EXTENDS Naturals

VARIABLE result, seq

InitInner == /\ result = 0
           /\ seq = <<1,2,3>>

Enabled == result = 0

Step == /\ Enabled
      /\ result' = 1
      /\ seq' = {x \in seq : x # result'}

SpecInner == InitInner /\ [][Step]_<<result, seq>>.

------------------------------------------------

------------------------------ MODULE Outer ------------------------------
INSTANCE Inner AS I WITH [result -> r, seq -> s]

VARIABLES r, s

InitOuter == /\ r = 0
           /\ s = <<1,2,3>>

Stutter == /\ r' = r
          /\ s' = s

Next == \/ I.Step
      \/ (Stutter /\ ~I.Enabled)

Spec == InitOuter /\ [][Next]_<<r,s>> /\ WF/I.Step /\ <> (~I.Enabled /\ []~I.Enabled).