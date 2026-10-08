MODULE OneVar

VARIABLE x

Init == 
    x = 0

Next ==
    \/ (x = 0 /\ x' \in {1,2})
    \/ (x # 0 /\ x' = 0)

StabilizeAwayFrom12 == 
    <> [] (x \notin {1,2})

RepeatedZero == 
    []<>(x = 0)

NotP == 
    []<>(x # 1)

PostCond ==
    /\ x \in {0,1,2}
    /\ LET rec == [a |-> 0, b |-> x] IN rec.b = x
    /\ LET tup == <<x, 0>> IN tup[1] = x
    /\ LET s == {rec.a, rec.b} IN s \subseteq {0,1,2}

Spec ==
    Init 
    /\ [][Next]_x 
    /\ WF_x(Next) 
    /\ StabilizeAwayFrom12 
    /\ RepeatedZero 
    /\ NotP 
    /\ PostCond

===============================================================================