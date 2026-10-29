---------------------------- MODULE PrimeTests ----------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLE x

Init == x = 1

Plus1(a) == a + 1
Same(a, b) == a = b
Double(a) == {a, a + a}

Check(cond, msg) == IF cond THEN TRUE ELSE Assert(FALSE, msg)

Next ==
  /\ x' = 2
  \* 1. Conditional expressions
  /\ Check(IF x' = 2 THEN TRUE ELSE FALSE, "Test 1a failed: IF condition on x'")
  /\ Check((IF x' > 1 THEN x' ELSE 0) = 2, "Test 1b failed: IF branch with x'")
  \* 2. Equality and inequality
  /\ Check(x' = 2, "Test 2a failed: x' = 2")
  /\ Check(x' # 3, "Test 2b failed: x' # 3")
  /\ Check(~(x' = 1), "Test 2c failed: ~(x' = 1)")
  \* 3. Set membership
  /\ Check(x' \in {1, 2}, "Test 3a failed: x' \\in {1,2}")
  /\ Check(x' \notin {3, 4}, "Test 3b failed: x' \\notin {3,4}")
  \* 4. Set construction
  /\ Check({x', x' + 1} = {2, 3}, "Test 4a failed: {x', x'+1}")
  /\ Check(1..x' = {1, 2}, "Test 4b failed: 1..x'")
  \* 5. Set comprehension
  /\ Check({y \in 1..5 : y > x'} = {3, 4, 5}, "Test 5a failed: filter with x'")
  /\ Check({y + x' : y \in {1, 2}} = {3, 4}, "Test 5b failed: map with x'")
  /\ Check({y \in 1..x' : TRUE} = {1, 2}, "Test 5c failed: filter over 1..x'")
  \* 6. Quantifiers
  /\ Check(\A y \in {x'} : y = 2, "Test 6a failed: \\A over {x'}")
  /\ Check(\E y \in 1..x' : y = 2, "Test 6b failed: \\E over 1..x'")
  /\ Check(~(\E y \in 1..5 : y = x' + 10), "Test 6c failed: ~\\E with x'")
  \* 7. CHOOSE
  /\ Check((CHOOSE y \in {x'} : TRUE) = 2, "Test 7a failed: CHOOSE from {x'}")
  /\ Check((CHOOSE y \in 1..5 : y = x') = 2, "Test 7b failed: CHOOSE y = x'")
  \* 8. SUBSET and UNION
  /\ Check(SUBSET {x'} = {{}, {2}}, "Test 8a failed: SUBSET {x'}")
  /\ Check(UNION {{x'}, {x' + 1}} = {2, 3}, "Test 8b failed: UNION with x'")
  \* 9. Function definitions (recursive)
  /\ LET f[n \in 0..x'] == IF n = 0 THEN 0 ELSE n + f[n - 1]
     IN Check(f[x'] = 3, "Test 9a failed: recursive function over x'")
  /\ LET g[n \in 1..3] == n * x'
     IN Check(g[3] = 6, "Test 9b failed: function body with x'")
  \* 10. Function application and domains
  /\ Check([y \in 1..3 |-> y * 2][x'] = 4, "Test 10a failed: application at x'")
  /\ Check(DOMAIN [y \in 1..x' |-> y] = {1, 2}, "Test 10b failed: DOMAIN with x'")
  \* 11. EXCEPT
  /\ Check([[y \in 1..3 |-> 0] EXCEPT ![x'] = x'] = [y \in 1..3 |-> IF y = 2 THEN 2 ELSE 0],
           "Test 11a failed: EXCEPT with x' index and value")
  /\ Check([[y \in 1..3 |-> y] EXCEPT ![1] = @ + x'][1] = 3, "Test 11b failed: EXCEPT @ + x'")
  \* 12. Function sets
  /\ Check([1..x' -> {x'}] = {[y \in 1..2 |-> 2]}, "Test 12a failed: [1..x' -> {x'}]")
  /\ Check(Cardinality([{x'} -> {1, 2, 3}]) = 3, "Test 12b failed: [{x'} -> S]")
  \* 13. Implication
  /\ Check((x' = 3) => FALSE, "Test 13a failed: false antecedent")
  /\ Check((x' = 2) => (x' > 1), "Test 13b failed: true antecedent")
  \* 14. CASE
  /\ CASE x' = 1 -> Assert(FALSE, "Test 14 failed: CASE chose x' = 1")
       [] x' = 2 -> TRUE
       [] OTHER  -> Assert(FALSE, "Test 14 failed: CASE chose OTHER")
  \* 15. Operator parameters
  /\ Check(Plus1(x') = 3, "Test 15a failed: Plus1(x')")
  /\ Check(Same(x', 2), "Test 15b failed: Same(x', 2)")
  /\ Check(Double(x') = {2, 4}, "Test 15c failed: Double(x')")

Spec == Init /\ [][Next]_x

Inv == x \in {1, 2}

=============================================================================