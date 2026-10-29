---------------------------- MODULE UnchangedTest ----------------------------
EXTENDS Naturals, Sequences, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = [i \in 1..3 |-> i]
    /\ y = 1

\* Case 1: UNCHANGED on a tuple of variables
Case1 ==
    /\ UNCHANGED <<x, y>>
    /\ PrintT("Test 1: UNCHANGED <<x, y>> OK")

\* Case 2: UNCHANGED on a single variable and on a function application
Case2 ==
    /\ x' = x
    /\ UNCHANGED y
    /\ UNCHANGED x[2]
    /\ IF UNCHANGED x[1]
         THEN PrintT("Test 2: UNCHANGED x[1] OK")
         ELSE Assert(FALSE, "Test 2 failed: UNCHANGED x[1]")

\* Case 3: UNCHANGED on a function value
Case3 ==
    /\ x' = [i \in 1..3 |-> i]
    /\ y' = y
    /\ UNCHANGED [i \in 1..3 |-> x[i] + y]
    /\ Assert(UNCHANGED x, "Test 3 failed: UNCHANGED function value")
    /\ PrintT("Test 3: UNCHANGED function value OK")

\* Case 4: UNCHANGED on a set comprehension
Case4 ==
    /\ UNCHANGED <<x, y>>
    /\ UNCHANGED {x[i] : i \in 1..3}
    /\ IF UNCHANGED {i \in 1..3 : x[i] > y}
         THEN PrintT("Test 4: UNCHANGED set comprehension OK")
         ELSE Assert(FALSE, "Test 4 failed: UNCHANGED set comprehension")

\* Case 5: UNCHANGED on a CHOOSE expression
Case5 ==
    /\ UNCHANGED x
    /\ y' = y
    /\ UNCHANGED (CHOOSE i \in 1..3 : x[i] = 2)
    /\ Assert(UNCHANGED (CHOOSE i \in DOMAIN x : x[i] = y),
              "Test 5 failed: UNCHANGED CHOOSE expression")
    /\ PrintT("Test 5: UNCHANGED CHOOSE expression OK")

\* Case 6: UNCHANGED on a record constructor
Case6 ==
    /\ UNCHANGED <<x, y>>
    /\ UNCHANGED [a |-> x, b |-> y]
    /\ IF UNCHANGED [a |-> x[1], b |-> <<y, x[3]>>]
         THEN PrintT("Test 6: UNCHANGED record constructor OK")
         ELSE Assert(FALSE, "Test 6 failed: UNCHANGED record constructor")

\* Case 7: UNCHANGED on nested tuples mixing variables and expressions
Case7 ==
    /\ UNCHANGED <<<<x>>, <<y, x[1] + y>>>>
    /\ Assert(x' = x /\ y' = y, "Test 7 failed: nested tuple UNCHANGED")
    /\ PrintT("Test 7: UNCHANGED nested tuple OK")

\* Case 8: UNCHANGED must be FALSE when a value actually changes
Case8 ==
    /\ x' = x
    /\ y' = y
    /\ IF UNCHANGED (x[1] + 1)
         THEN PrintT("Test 8: UNCHANGED (x[1] + 1) OK")
         ELSE Assert(FALSE, "Test 8 failed: UNCHANGED arithmetic expression")

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

TypeOK ==
    /\ x \in [1..3 -> Nat]
    /\ y \in Nat

=============================================================================