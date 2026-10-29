------------------------------- MODULE TestUnchanged -------------------------------
EXTENDS Naturals, Sequences, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = [i \in 1..3 |-> i]
    /\ y = 1

\* Case 1: UNCHANGED on a tuple of variables
Case1 ==
    /\ UNCHANGED <<x, y>>
    /\ Print("Test 1: UNCHANGED <<x, y>> OK", TRUE)

\* Case 2: UNCHANGED on a function application (x[1]) while x is modified elsewhere
Case2 ==
    /\ x' = [x EXCEPT ![2] = 2]
    /\ y' = y
    /\ IF UNCHANGED x[1]
         THEN Print("Test 2: UNCHANGED x[1] OK", TRUE)
         ELSE Assert(FALSE, "Test 2 failed: UNCHANGED x[1]")

\* Case 3: UNCHANGED on a whole function value
Case3 ==
    /\ x' = [i \in 1..3 |-> i]
    /\ y' = y
    /\ IF UNCHANGED x
         THEN Print("Test 3: UNCHANGED x (function value) OK", TRUE)
         ELSE Assert(FALSE, "Test 3 failed: UNCHANGED x")

\* Case 4: UNCHANGED on a set comprehension
Case4 ==
    /\ x' = x
    /\ y' = y
    /\ IF UNCHANGED {x[i] + y : i \in 1..3}
         THEN Print("Test 4: UNCHANGED set comprehension OK", TRUE)
         ELSE Assert(FALSE, "Test 4 failed: UNCHANGED set comprehension")

\* Case 5: UNCHANGED on a set filter
Case5 ==
    /\ x' = x
    /\ y' = y
    /\ IF UNCHANGED {i \in 1..3 : x[i] > y}
         THEN Print("Test 5: UNCHANGED set filter OK", TRUE)
         ELSE Assert(FALSE, "Test 5 failed: UNCHANGED set filter")

\* Case 6: UNCHANGED on a CHOOSE expression
Case6 ==
    /\ x' = x
    /\ y' = y
    /\ IF UNCHANGED (CHOOSE i \in 1..3 : x[i] = y)
         THEN Print("Test 6: UNCHANGED CHOOSE OK", TRUE)
         ELSE Assert(FALSE, "Test 6 failed: UNCHANGED CHOOSE")

\* Case 7: UNCHANGED on a record constructor
Case7 ==
    /\ x' = x
    /\ y' = y
    /\ IF UNCHANGED [a |-> x, b |-> y]
         THEN Print("Test 7: UNCHANGED record constructor OK", TRUE)
         ELSE Assert(FALSE, "Test 7 failed: UNCHANGED record constructor")

\* Case 8: UNCHANGED on a function constructor built from variables
Case8 ==
    /\ x' = x
    /\ y' = y
    /\ IF UNCHANGED [i \in 1..3 |-> x[i] + y]
         THEN Print("Test 8: UNCHANGED function constructor OK", TRUE)
         ELSE Assert(FALSE, "Test 8 failed: UNCHANGED function constructor")

\* Case 9: UNCHANGED on a nested tuple
Case9 ==
    /\ x' = x
    /\ y' = y
    /\ IF UNCHANGED <<<<x>>, <<y, x[3]>>>>
         THEN Print("Test 9: UNCHANGED nested tuple OK", TRUE)
         ELSE Assert(FALSE, "Test 9 failed: UNCHANGED nested tuple")

\* Case 10: a change must be detected (negative test)
Case10 ==
    /\ x' = x
    /\ y' = y + 1
    /\ IF ~ UNCHANGED <<x, y>>
         THEN Print("Test 10: change to y detected OK", TRUE)
         ELSE Assert(FALSE, "Test 10 failed: UNCHANGED <<x, y>> should be FALSE")
    /\ y' = 2

Next ==
    \/ Case1
    \/ Case2
    \/ Case3
    \/ Case4
    \/ Case5
    \/ Case6
    \/ Case7
    \/ Case8
    \/ Case9
    \/ Case10

Spec == Init /\ [][Next]_vars

Inv == TRUE

=============================================================================