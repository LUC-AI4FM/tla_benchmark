---------------------------- MODULE UnchangedTest ----------------------------
EXTENDS Naturals, Sequences, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = [i \in 1..3 |-> i]
    /\ y = 1

\* Case 1: UNCHANGED on a tuple of variables
Case1 ==
    /\ y = 1
    /\ UNCHANGED <<x, y>>
    /\ PrintT("Test 1: UNCHANGED <<x, y>> succeeded")

\* Case 2: UNCHANGED on a function application
Case2 ==
    /\ y = 1
    /\ x' = [x EXCEPT ![2] = 2]
    /\ UNCHANGED x[2]
    /\ UNCHANGED y
    /\ PrintT("Test 2: UNCHANGED x[2] succeeded")

\* Case 3: UNCHANGED on a function value (constructor)
Case3 ==
    /\ y = 1
    /\ UNCHANGED [i \in 1..3 |-> x[i] + y]
    /\ UNCHANGED <<x, y>>
    /\ Assert(x' = x /\ y' = y, "Test 3 failed")
    /\ PrintT("Test 3: UNCHANGED function constructor succeeded")

\* Case 4: UNCHANGED on a set comprehension
Case4 ==
    /\ y = 1
    /\ UNCHANGED x
    /\ y' = 1
    /\ UNCHANGED {x[i] : i \in 1..3}
    /\ UNCHANGED {i \in 1..3 : x[i] > y}
    /\ PrintT("Test 4: UNCHANGED set comprehension succeeded")

\* Case 5: UNCHANGED on a CHOOSE expression
Case5 ==
    /\ y = 1
    /\ UNCHANGED <<x, y>>
    /\ UNCHANGED (CHOOSE i \in 1..3 : x[i] = y)
    /\ Assert((CHOOSE i \in 1..3 : x'[i] = y') = (CHOOSE i \in 1..3 : x[i] = y),
              "Test 5 failed")
    /\ PrintT("Test 5: UNCHANGED CHOOSE succeeded")

\* Case 6: UNCHANGED on a record constructor
Case6 ==
    /\ y = 1
    /\ UNCHANGED [a |-> x, b |-> y]
    /\ Assert(x' = x /\ y' = y, "Test 6 failed")
    /\ PrintT("Test 6: UNCHANGED record constructor succeeded")

\* Case 7: UNCHANGED of a nested tuple
Case7 ==
    /\ y = 1
    /\ UNCHANGED <<<<x>>, <<y, x>>>>
    /\ Assert(x' = x /\ y' = y, "Test 7 failed")
    /\ PrintT("Test 7: UNCHANGED nested tuple succeeded")

Next ==
    \/ Case1
    \/ Case2
    \/ Case3
    \/ Case4
    \/ Case5
    \/ Case6
    \/ Case7

Spec == Init /\ [][Next]_vars

Inv == TRUE

=============================================================================