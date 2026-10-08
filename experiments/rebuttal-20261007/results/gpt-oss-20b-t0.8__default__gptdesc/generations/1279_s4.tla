MODULE SmallModel
EXTENDS Naturals

VARIABLE s

Init ==
    /\ s = 23

Next ==
    \E v \in 0..1 : (v > 0 /\ s' = v)

Inv ==
    s # 0

Spec ==
    Init /\ [][Next]_s /\ []Inv

===============================================================================