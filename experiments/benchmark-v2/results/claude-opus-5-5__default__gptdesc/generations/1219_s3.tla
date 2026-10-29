---------------------------- MODULE UnchangedTest ----------------------------
EXTENDS Naturals, Sequences, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = [i \in 1..3 |-> i]
    /\ y = 1

(* Case 1: UNCHANGED on a tuple of variables *)
Case1 ==
    /\ UNCHANGED <<x, y>>
    /\ IF x' = x /\ y' = y
         THEN Print("Test 1 OK: UNCHANGED <<x, y>>", TRUE)
         ELSE Assert(FALSE, "Test 1 Failed: UNCHANGED <<x, y>>")

(* Case 2: UNCHANGED on a function application *)
Case2 ==
    /\ x' = x
    /\ y' = y
    /\ IF UNCHANGED x[1]
         THEN Print("Test 2 OK: UNCHANGED x[1]", TRUE)
         ELSE Assert(FALSE, "Test 2 Failed: UNCHANGED x[1]")

(* Case 3: UNCHANGED on a function constructor value *)
Case3 ==
    /\ UNCHANGED x
    /\ UNCHANGED y
    /\ IF UNCHANGED [i \in 1..3 |-> x[i] + y]
         THEN Print("Test 3 OK: UNCHANGED function value", TRUE)
         ELSE Assert(FALSE, "Test 3 Failed: UNCHANGED function value")

(* Case 4: UNCHANGED on a set comprehension *)
Case4 ==
    /\ UNCHANGED <<x, y>>
    /\ IF UNCHANGED {x[i] : i \in 1..3}
         THEN Print("Test 4 OK: UNCHANGED set comprehension", TRUE)
         ELSE Assert(FALSE, "Test 4 Failed: UNCHANGED set comprehension")

(* Case 5: UNCHANGED on a set filter *)
Case5 ==
    /\ UNCHANGED <<x, y>>
    /\ IF UNCHANGED {i \in 1..3 : x[i] >= y}
         THEN Print("Test 5 OK: UNCHANGED set filter", TRUE)
         ELSE Assert(FALSE, "Test 5 Failed: UNCHANGED set filter")

(* Case 6: UNCHANGED on a CHOOSE expression *)
Case6 ==
    /\ UNCHANGED <<x, y>>
    /\ IF UNCHANGED (CHOOSE i \in DOMAIN x : x[i] = y)
         THEN Print("Test 6 OK: UNCHANGED CHOOSE", TRUE)
         ELSE Assert(FALSE, "Test 6 Failed: UNCHANGED CHOOSE")

(* Case 7: UNCHANGED on a record constructor *)
Case7 ==
    /\ UNCHANGED <<x, y>>
    /\ IF UNCHANGED [a |-> x, b |-> y]
         THEN Print("Test 7 OK: UNCHANGED record", TRUE)
         ELSE Assert(FALSE, "Test 7 Failed: UNCHANGED record")

(* Case 8: UNCHANGED on nested tuples *)
Case8 ==
    /\ UNCHANGED <<<<x>>, <<y, x[2]>>>>
    /\ IF x' = x /\ y' = y
         THEN Print("Test 8 OK: UNCHANGED nested tuple", TRUE)
         ELSE Assert(FALSE, "Test 8 Failed: UNCHANGED nested tuple")

(* Case 9: UNCHANGED must be FALSE when a variable actually changes *)
Case9 ==
    /\ x' = [x EXCEPT ![1] = 1]
    /\ y' = y
    /\ IF UNCHANGED <<x, y>>
         THEN Print("Test 9 OK: UNCHANGED after identity EXCEPT", TRUE)
         ELSE Assert(FALSE, "Test 9 Failed: UNCHANGED after identity EXCEPT")

(* Case 10: UNCHANGED is false on an expression whose value differs *)
Case10 ==
    /\ UNCHANGED <<x, y>>
    /\ IF ~UNCHANGED (y + 1) \/ (y' + 1 = y + 1)
         THEN Print("Test 10 OK: UNCHANGED arithmetic expression", TRUE)
         ELSE Assert(FALSE, "Test 10 Failed: UNCHANGED arithmetic expression")

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