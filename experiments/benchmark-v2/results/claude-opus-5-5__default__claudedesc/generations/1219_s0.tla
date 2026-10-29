------------------------------ MODULE UnchangedTest ------------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = [i \in 1..3 |-> i]
    /\ y = 1

Check(cond, n) ==
    IF cond
       THEN Print(<<"Test", n, "OK">>, TRUE)
       ELSE Assert(FALSE, <<"Test", n, "Failed">>)

Test1 ==
    /\ x' = x /\ y' = y
    /\ Check(UNCHANGED x[1], 1)

Test2 ==
    /\ x' = x /\ y' = y
    /\ Check(UNCHANGED [a |-> x[1], b |-> x[2]], 2)

Test3 ==
    /\ x' = x /\ y' = y
    /\ Check(UNCHANGED (\E i \in 1..3 : x[i] = 2), 3)

Test4 ==
    /\ x' = x /\ y' = y
    /\ Check(UNCHANGED (\A i \in 1..3 : x[i] > 0), 4)

Test5 ==
    /\ x' = x /\ y' = y
    /\ Check(UNCHANGED (CHOOSE i \in 1..3 : x[i] = 3), 5)

Test6 ==
    /\ x' = x /\ y' = y
    /\ Check(UNCHANGED {x[i] + 1 : i \in 1..3}, 6)

Test7 ==
    /\ x' = x /\ y' = y
    /\ Check(UNCHANGED {i \in 1..3 : x[i] > 1}, 7)

Test8 ==
    /\ x' = x /\ y' = y
    /\ Check(UNCHANGED DOMAIN x, 8)

Test9 ==
    /\ x' = x /\ y' = y
    /\ Check(UNCHANGED <<x[1], x[2], x[3], y>>, 9)

Test10 ==
    /\ y = 1
    /\ x' = x
    /\ y' = y + 1
    /\ Check(UNCHANGED <<x, x[1], {x[i] : i \in DOMAIN x}>>, 10)

Test11 ==
    /\ y = 1
    /\ x' = x
    /\ y' = y + 1
    /\ Check(UNCHANGED {e \in {1, 2, 3} : x[e] = 1}, 11)

Next ==
    \/ Test1
    \/ Test2
    \/ Test3
    \/ Test4
    \/ Test5
    \/ Test6
    \/ Test7
    \/ Test8
    \/ Test9
    \/ Test10
    \/ Test11

Spec == Init /\ [][Next]_vars

Inv == TRUE

==================================================================================