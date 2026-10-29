------------------------------- MODULE PrimeTest -------------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init == /\ x = 1
        /\ y = 1

Plus1(a) == a + 1

Check(cond, msg) == IF cond THEN Assert(FALSE, msg) ELSE TRUE

TNext ==
  /\ x' = x + 1
  /\ x' = 2
  /\ \/ /\ y' = y
        /\ Check((IF x' = 2 THEN 1 ELSE 0) # 1, "Test 1 (IF) failed")
     \/ /\ y' = 1
        /\ Check(x' \notin {1, 2}, "Test 2 (set membership) failed")
     \/ /\ y' = 1
        /\ Check({x', y'} # {1, 2}, "Test 3 (set enumeration) failed")
     \/ /\ y' = 1
        /\ Check(~ \E i \in {1, 2, 3} : i = x', "Test 4 (existential) failed")
     \/ /\ y' = 1
        /\ Check(~ \A i \in {x'} : i = 2, "Test 5 (universal) failed")
     \/ /\ y' = 1
        /\ Check((CHOOSE i \in {1, 2, 3} : i = x') # 2, "Test 6 (CHOOSE) failed")
     \/ /\ y' = 1
        /\ Check([i \in {1, 2} |-> i + x'][1] # 3, "Test 7 (function) failed")
     \/ /\ y' = 1
        /\ Check([[i \in {1, 2} |-> i] EXCEPT ![1] = x'][1] # 2,
                 "Test 8 (EXCEPT) failed")
     \/ /\ y' = 1
        /\ Check({x'} \notin SUBSET {1, 2}, "Test 9 (SUBSET) failed")
     \/ /\ y' = 1
        /\ Check(UNION {{x'}, {y'}} # {1, 2}, "Test 10 (UNION) failed")
     \/ /\ y' = 1
        /\ Check([i \in {1} |-> x'] \notin [{1} -> {2}],
                 "Test 11 (function space) failed")
     \/ /\ y' = 1
        /\ Check(~(x' = 2 => y' = 1), "Test 12 (implication) failed")
     \/ /\ y' = 1
        /\ Check(CASE x' = 1 -> TRUE
                   [] x' = 2 -> FALSE
                   [] OTHER  -> TRUE, "Test 13 (CASE) failed")
     \/ /\ y' = 1
        /\ Check(Plus1(x') # 3, "Test 14 (operator application) failed")
     \/ /\ y' = 1
        /\ Check({i + x' : i \in {1}} # {3}, "Test 15 (set map) failed")
     \/ /\ y' = 1
        /\ Check({i \in {1, 2, 3} : i = x'} # {2}, "Test 16 (set filter) failed")

Next == TNext \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv == TRUE

=============================================================================