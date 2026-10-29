------------------------------ MODULE PrimeTests ------------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init == /\ x = 1
        /\ y = 1

Op(a) == a + 1

Op2(a, b) == a + b

TNext ==
  /\ x = 1
  /\ x' = 2
  /\ \/ y' = y
     \/ y' = 1
     \/ /\ y' = 1
        /\ IF x' = 2 THEN FALSE ELSE TRUE
        /\ Assert(FALSE, "Test 1 Failed")
     \/ /\ y' = 1
        /\ x' \notin {2}
        /\ Assert(FALSE, "Test 2 Failed")
     \/ /\ y' = 1
        /\ ~(x' \in {x', 3})
        /\ Assert(FALSE, "Test 3 Failed")
     \/ /\ y' = 1
        /\ {x', y'} # {1, 2}
        /\ Assert(FALSE, "Test 4 Failed")
     \/ /\ y' = 1
        /\ ~(\E i \in {1, 2} : i = x')
        /\ Assert(FALSE, "Test 5 Failed")
     \/ /\ y' = 1
        /\ ~(\A i \in {x'} : i = 2)
        /\ Assert(FALSE, "Test 6 Failed")
     \/ /\ y' = 1
        /\ (CHOOSE i \in {1, 2} : i = x') # 2
        /\ Assert(FALSE, "Test 7 Failed")
     \/ /\ y' = 1
        /\ [i \in {1, 2} |-> i + x'][1] # 3
        /\ Assert(FALSE, "Test 8 Failed")
     \/ /\ y' = 1
        /\ [[i \in {1, 2} |-> i] EXCEPT ![1] = x'][1] # 2
        /\ Assert(FALSE, "Test 9 Failed")
     \/ /\ y' = 1
        /\ [[i \in {1, 2} |-> i] EXCEPT ![x'] = 7][2] # 7
        /\ Assert(FALSE, "Test 10 Failed")
     \/ /\ y' = 1
        /\ {x'} \notin SUBSET {1, 2}
        /\ Assert(FALSE, "Test 11 Failed")
     \/ /\ y' = 1
        /\ UNION {{x'}, {y'}} # {1, 2}
        /\ Assert(FALSE, "Test 12 Failed")
     \/ /\ y' = 1
        /\ [i \in {1} |-> x'] \notin [{1} -> {2}]
        /\ Assert(FALSE, "Test 13 Failed")
     \/ /\ y' = 1
        /\ ~(x' = 2 => y' = 1)
        /\ Assert(FALSE, "Test 14 Failed")
     \/ /\ y' = 1
        /\ CASE x' = 1 -> TRUE
             [] x' = 2 -> FALSE
             [] OTHER  -> TRUE
        /\ Assert(FALSE, "Test 15 Failed")
     \/ /\ y' = 1
        /\ Op(x') # 3
        /\ Assert(FALSE, "Test 16 Failed")
     \/ /\ y' = 1
        /\ Op2(x', y') # 3
        /\ Assert(FALSE, "Test 17 Failed")
     \/ /\ y' = 1
        /\ {i \in {1, 2, 3} : i > x'} # {3}
        /\ Assert(FALSE, "Test 18 Failed")
     \/ /\ y' = 1
        /\ {i + x' : i \in {1}} # {3}
        /\ Assert(FALSE, "Test 19 Failed")
     \/ /\ y' = 1
        /\ LET z == x' IN z # 2
        /\ Assert(FALSE, "Test 20 Failed")
     \/ /\ y' = 1
        /\ <<x', y'>> # <<2, 1>>
        /\ Assert(FALSE, "Test 21 Failed")
     \/ /\ y' = 1
        /\ [a |-> x'].a # 2
        /\ Assert(FALSE, "Test 22 Failed")

Next == TNext \/ UNCHANGED vars

Inv == TRUE

Spec == Init /\ [][Next]_vars
=============================================================================