MODULE OneVarSys
EXTENDS TLC

VARIABLE x

Init == 
    x = 0

Next ==
    \/ (x = 0 /\ x' ∈ {1,2})
    \/ (x # 0 /\ x' = 0)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

SafetyInvariant == [] (x ∈ {0,1,2})

P1 == <>[] (x = 0)
P2 == []<>(x = 0)
NegP1 == ~(<>[] (x = 0))

RecordExample == [a : 1, b : {2,3}]
TupleExample   == <<1, 2>>
SetExample     == {1, 2}

PostCond ==
    /\ RecordExample.b = {2,3}
    /\ TupleExample[2] = 2
    /\ SetExample # {}