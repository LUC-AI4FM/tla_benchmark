------------------------------- MODULE UnchangedTest -------------------------------
EXTENDS Naturals, Sequences, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = [i \in 1..3 |-> i]
    /\ y = 1

\* Case 1: UNCHANGED on a tuple of variables
Case1 ==
    /\ UNCHANGED <<x, y>>
    /\ Print("Test 1 (UNCHANGED tuple) OK", TRUE)

\* Case 2: UNCHANGED on a variable followed by UNCHANGED of a function value
Case2 ==
    /\ x' = x
    /\ y' = y
    /\ IF UNCHANGED [i \in 1..3 |-> x[i]]
         THEN Print("Test 2 (UNCHANGED function value) OK", TRUE)
         ELSE Assert(FALSE, "Test 2 (UNCHANGED function value) FAILED")

\* Case 3: UNCHANGED on a set comprehension
Case3 ==
    /\ UNCHANGED x
    /\ UNCHANGED y
    /\ IF UNCHANGED {x[i] : i \in 1..3}
         THEN Print("Test 3 (UNCHANGED set comprehension) OK", TRUE)
         ELSE Assert(FALSE, "Test 3 (UNCHANGED set comprehension) FAILED")

\* Case 4: UNCHANGED on a CHOOSE expression
Case4 ==
    /\ UNCHANGED <<x, y>>
    /\ IF UNCHANGED (CHOOSE i \in DOMAIN x : x[i] = x[2])
         THEN Print("Test 4 (UNCHANGED CHOOSE) OK", TRUE)
         ELSE Assert(FALSE, "Test 4 (UNCHANGED CHOOSE) FAILED")

\* Case 5: UNCHANGED on a record constructor
Case5 ==
    /\ UNCHANGED <<x, y>>
    /\ IF UNCHANGED [a |-> x, b |-> y]
         THEN Print("Test 5 (UNCHANGED record) OK", TRUE)
         ELSE Assert(FALSE, "Test 5 (UNCHANGED record) FAILED")

\* Case 6: UNCHANGED on a nested tuple containing expressions
Case6 ==
    /\ UNCHANGED <<x, <<y, x[1]>>>>
    /\ IF UNCHANGED <<x[1] + y, {y}>>
         THEN Print("Test 6 (UNCHANGED nested tuple) OK", TRUE)
         ELSE Assert(FALSE, "Test 6 (UNCHANGED nested tuple) FAILED")

\* Case 7: UNCHANGED must be FALSE when a variable actually changes
Case7 ==
    /\ x' = [x EXCEPT ![1] = 5]
    /\ y' = y
    /\ IF x[1] # 5
         THEN IF UNCHANGED x
                THEN Assert(FALSE, "Test 7 (UNCHANGED detects change) FAILED")
                ELSE Print("Test 7 (UNCHANGED detects change) OK", TRUE)
         ELSE Print("Test 7 skipped (x[1] already 5)", TRUE)

\* Case 8: UNCHANGED on an expression that is invariant even though a variable changes
Case8 ==
    /\ x' = x
    /\ y' = IF y = 1 THEN 2 ELSE 1
    /\ IF UNCHANGED (y \in {1, 2})
         THEN Print("Test 8 (UNCHANGED invariant expression) OK", TRUE)
         ELSE Assert(FALSE, "Test 8 (UNCHANGED invariant expression) FAILED")
    /\ IF UNCHANGED y
         THEN Assert(FALSE, "Test 8b (UNCHANGED y) FAILED")
         ELSE Print("Test 8b (UNCHANGED y detects change) OK", TRUE)

Next ==
    \/ Case1
    \/ Case2
    \/ Case3
    \/ Case4
    \/ Case5
    \/ Case6
    \/ Case7
    \/ Case8

Spec == Init /\ [][Next]_vars

Inv == TRUE

=============================================================================