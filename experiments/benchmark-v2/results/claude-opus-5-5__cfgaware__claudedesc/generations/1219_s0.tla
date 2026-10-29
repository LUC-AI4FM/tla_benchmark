---------------------------- MODULE Unchanged ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
  /\ x = [i \in 1..3 |-> i]
  /\ y = 1

Test1 ==
  /\ UNCHANGED vars
  /\ IF UNCHANGED x[1]
       THEN Print("Test 1 OK", TRUE)
       ELSE Assert(FALSE, "Test 1 Failed")

Test2 ==
  /\ UNCHANGED vars
  /\ IF UNCHANGED [a |-> x[1], b |-> x[2]]
       THEN Print("Test 2 OK", TRUE)
       ELSE Assert(FALSE, "Test 2 Failed")

Test3 ==
  /\ UNCHANGED vars
  /\ IF UNCHANGED (\E i \in 1..3 : x[i] = 2)
       THEN Print("Test 3 OK", TRUE)
       ELSE Assert(FALSE, "Test 3 Failed")

Test4 ==
  /\ UNCHANGED vars
  /\ IF UNCHANGED (\A i \in 1..3 : x[i] > 0)
       THEN Print("Test 4 OK", TRUE)
       ELSE Assert(FALSE, "Test 4 Failed")

Test5 ==
  /\ UNCHANGED vars
  /\ IF UNCHANGED (CHOOSE i \in 1..3 : x[i] = 3)
       THEN Print("Test 5 OK", TRUE)
       ELSE Assert(FALSE, "Test 5 Failed")

Test6 ==
  /\ UNCHANGED vars
  /\ IF UNCHANGED {x[i] : i \in 1..3}
       THEN Print("Test 6 OK", TRUE)
       ELSE Assert(FALSE, "Test 6 Failed")

Test7 ==
  /\ UNCHANGED vars
  /\ IF UNCHANGED {i \in 1..3 : x[i] > 1}
       THEN Print("Test 7 OK", TRUE)
       ELSE Assert(FALSE, "Test 7 Failed")

Test8 ==
  /\ UNCHANGED vars
  /\ IF UNCHANGED DOMAIN x
       THEN Print("Test 8 OK", TRUE)
       ELSE Assert(FALSE, "Test 8 Failed")

Test9 ==
  /\ UNCHANGED vars
  /\ IF UNCHANGED <<x[1], x[2], x[3]>>
       THEN Print("Test 9 OK", TRUE)
       ELSE Assert(FALSE, "Test 9 Failed")

Test10 ==
  /\ y = 1
  /\ y' = y + 1
  /\ UNCHANGED x
  /\ IF UNCHANGED <<x, x[1]>>
       THEN Print("Test 10 OK", TRUE)
       ELSE Assert(FALSE, "Test 10 Failed")

Test11 ==
  /\ y = 1
  /\ y' = y + 1
  /\ UNCHANGED x
  /\ IF UNCHANGED ({y} \cup {x[1], x[2]})
       THEN Print("Test 11 OK", TRUE)
       ELSE Assert(FALSE, "Test 11 Failed")

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

=============================================================================