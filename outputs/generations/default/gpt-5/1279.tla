---- MODULE SmallTemporal ----
EXTENDS Naturals

CONSTANTS DummyConst

VARIABLES s

Init == s = 23

Next(var) == \E v \in 0..1: /\ s' = v
                          /\ v > 0

Inv == s # 0

Spec == Init /\ [] [Next(s)]_s

====