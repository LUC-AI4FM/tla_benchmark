---------------------------- MODULE Test_Unchanged ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = [i \in 1..3 |-> i]
    /\ y = 1

\* Case 1: UNCHANGED on a tuple of variables
Case1 ==
    /\ UNCHANGED <<x, y>>
    /\ Print("Test 1: UNCHANGED <<x, y>> OK", TRUE)

\* Case 2: UNCHANGED on a single variable, other variable explicitly kept
Case2 ==
    /\ x' = x
    /\ UNCHANGED y
    /\ Assert(y' = y, "Test 2 failed: UNCHANGED y")
    /\ Print("Test 2: UNCHANGED y OK", TRUE)

\* Case 3: UNCHANGED on a function application
Case3 ==
    /\ x' = [x EXCEPT ![2] = x[2]]
    /\ y' = y
    /\ UNCHANGED x[1]
    /\ UNCHANGED x[2]
    /\ UNCHANGED x[3]
    /\ Assert(x' = x, "Test 3 failed: UNCHANGED x[i]")
    /\ Print("Test 3: UNCHANGED function application OK", TRUE)

\* Case 4: UNCHANGED on a function value constructed from x
Case4 ==
    /\ UNCHANGED x
    /\ UNCHANGED y
    /\ UNCHANGED [i \in 1..3 |-> x[i] + y]
    /\ Print("Test 4: UNCHANGED function constructor OK", TRUE)

\* Case 5: UNCHANGED on a set comprehension
Case5 ==
    /\ UNCHANGED <<x, y>>
    /\ UNCHANGED {x[i] : i \in 1..3}
    /\ UNCHANGED {i \in 1..3 : x[i] > y}
    /\ Assert({x'[i] : i \in 1..3} = {x[i] : i \in 1..3},
              "Test 5 failed: UNCHANGED set comprehension")
    /\ Print("Test 5: UNCHANGED set comprehension OK", TRUE)

\* Case 6: UNCHANGED on a CHOOSE expression
Case6 ==
    /\ UNCHANGED <<x, y>>
    /\ UNCHANGED (CHOOSE i \in 1..3 : x[i] = y)
    /\ Assert((CHOOSE i \in 1..3 : x'[i] = y') = (CHOOSE i \in 1..3 : x[i] = y),
              "Test 6 failed: UNCHANGED CHOOSE")
    /\ Print("Test 6: UNCHANGED CHOOSE OK", TRUE)

\* Case 7: UNCHANGED on a record constructor
Case7 ==
    /\ UNCHANGED <<x, y>>
    /\ UNCHANGED [a |-> x, b |-> y]
    /\ Assert([a |-> x', b |-> y'] = [a |-> x, b |-> y],
              "Test 7 failed: UNCHANGED record")
    /\ Print("Test 7: UNCHANGED record constructor OK", TRUE)

\* Case 8: UNCHANGED on nested tuples
Case8 ==
    /\ UNCHANGED <<<<x>>, <<y, <<x, y>>>>>>
    /\ Assert(x' = x /\ y' = y, "Test 8 failed: UNCHANGED nested tuple")
    /\ Print("Test 8: UNCHANGED nested tuple OK", TRUE)

\* Case 9: UNCHANGED on an expression that is changed must be FALSE
Case9 ==
    /\ x' = x
    /\ y' = y
    /\ IF UNCHANGED (y + 1)
         THEN Print("Test 9: UNCHANGED (y+1) OK", TRUE)
         ELSE Assert(FALSE, "Test 9 failed: UNCHANGED (y+1)")

\* Case 10: UNCHANGED vars where vars is a defined tuple
Case10 ==
    /\ UNCHANGED vars
    /\ Assert(vars' = vars, "Test 10 failed: UNCHANGED vars")
    /\ Print("Test 10: UNCHANGED vars OK", TRUE)

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