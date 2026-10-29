---------------------------- MODULE PrimeExprTest ----------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLE x

vars == <<x>>

(***************************************************************************)
(* Helper: succeeds only if the condition is TRUE; otherwise raises an     *)
(* assertion failure with a descriptive message.                           *)
(***************************************************************************)
Check(cond, msg) == IF cond THEN TRUE ELSE Assert(FALSE, msg)

(***************************************************************************)
(* User-defined operators used to pass primed expressions as parameters.   *)
(***************************************************************************)
Plus(a, b)      == a + b
Twice(a)        == a * 2
InSet(a, S)     == a \in S
NextVal         == x'
ApplyOp(Op(_), a) == Op(a)
Inc(a)          == a + 1

Init == x = 1

PrimeTests ==
  \* 1. Conditional expressions
  /\ IF x' = 2 THEN TRUE ELSE Assert(FALSE, "Test 1a failed: IF condition on x'")
  /\ Check((IF x' > 1 THEN x' ELSE 0) = 2, "Test 1b failed: IF branch with x'")
  /\ Check((IF x' = 1 THEN 10 ELSE x' + 10) = 12, "Test 1c failed: IF else-branch with x'")
  \* 2. Equality and inequality
  /\ Check(x' = 2, "Test 2a failed: x' = 2")
  /\ Check(x' # 1, "Test 2b failed: x' # 1")
  /\ Check(x' = x + 1, "Test 2c failed: x' = x + 1")
  /\ Check(~(x' = x), "Test 2d failed: ~(x' = x)")
  \* 3. Set membership
  /\ Check(x' \in {2, 3}, "Test 3a failed: x' \\in {2,3}")
  /\ Check(x' \notin {1}, "Test 3b failed: x' \\notin {1}")
  /\ Check(x' \in 1..x', "Test 3c failed: x' \\in 1..x'")
  \* 4. Set construction
  /\ Check({x', x} = {1, 2}, "Test 4a failed: {x', x}")
  /\ Check({x'} = {2}, "Test 4b failed: {x'}")
  /\ Check(Cardinality({x, x'}) = 2, "Test 4c failed: Cardinality({x, x'})")
  /\ Check(x..x' = {1, 2}, "Test 4d failed: x..x'")
  \* 5. Set comprehension (filter and map)
  /\ Check({y \in 1..5 : y > x'} = {3, 4, 5}, "Test 5a failed: set filter with x'")
  /\ Check({y + x' : y \in {0, 1}} = {2, 3}, "Test 5b failed: set map with x'")
  /\ Check({y \in {x'} : y = 2} = {2}, "Test 5c failed: filter over {x'}")
  \* 6. Quantifiers
  /\ Check(\A y \in {x'} : y = 2, "Test 6a failed: \\A over {x'}")
  /\ Check(\E y \in 1..x' : y = 2, "Test 6b failed: \\E over 1..x'")
  /\ Check(\A y \in 1..x' : y <= x', "Test 6c failed: \\A y <= x'")
  /\ Check(~(\E y \in 1..5 : y = x' /\ y = 3), "Test 6d failed: negated \\E with x'")
  \* 7. CHOOSE
  /\ Check((CHOOSE y \in {x'} : TRUE) = 2, "Test 7a failed: CHOOSE from {x'}")
  /\ Check((CHOOSE y \in 1..5 : y = x') = 2, "Test 7b failed: CHOOSE y = x'")
  \* 8. SUBSET and UNION
  /\ Check(SUBSET {x'} = {{}, {2}}, "Test 8a failed: SUBSET {x'}")
  /\ Check(UNION {{x}, {x'}} = {1, 2}, "Test 8b failed: UNION {{x},{x'}}")
  /\ Check(Cardinality(SUBSET (1..x')) = 4, "Test 8c failed: SUBSET 1..x'")
  \* 9. Function definitions (parameterized and recursive)
  /\ LET f[i \in 1..3] == i + x'
     IN  Check(f[1] = 3 /\ f[3] = 5, "Test 9a failed: function defined with x'")
  /\ LET fact[n \in 0..x'] == IF n = 0 THEN 1 ELSE n * fact[n - 1]
     IN  Check(fact[x'] = 2, "Test 9b failed: recursive function over 0..x'")
  /\ LET sum[n \in 0..3] == IF n = 0 THEN x' ELSE x' + sum[n - 1]
     IN  Check(sum[3] = 8, "Test 9c failed: recursive function body with x'")
  \* 10. Function application and domains
  /\ LET g == [i \in 1..x' |-> i * 2]
     IN  /\ Check(g[x'] = 4, "Test 10a failed: g[x']")
         /\ Check(DOMAIN g = 1..2, "Test 10b failed: DOMAIN g")
  /\ Check([i \in {x'} |-> i][2] = 2, "Test 10c failed: [i \\in {x'} |-> i][2]")
  \* 11. EXCEPT
  /\ Check([[i \in 1..3 |-> 0] EXCEPT ![x'] = x']
              = [i \in 1..3 |-> IF i = 2 THEN 2 ELSE 0],
           "Test 11a failed: EXCEPT with x' index and value")
  /\ Check([[i \in 1..3 |-> 1] EXCEPT ![1] = @ + x'][1] = 3,
           "Test 11b failed: EXCEPT with @ + x'")
  /\ Check([[i \in 1..x' |-> i] EXCEPT ![x] = x'] = [i \in 1..2 |-> 2],
           "Test 11c failed: EXCEPT over domain 1..x'")
  \* 12. Function sets
  /\ Check([{x'} -> {x}] = {[i \in {2} |-> 1]}, "Test 12a failed: [{x'} -> {x}]")
  /\ Check(Cardinality([1..x' -> {0, 1}]) = 4, "Test 12b failed: [1..x' -> {0,1}]")
  /\ Check([i \in {1} |-> x'] \in [{1} -> {x'}], "Test 12c failed: range {x'}")
  \* 13. Implication
  /\ Check((x' = 2) => (x' > 1), "Test 13a failed: true antecedent")
  /\ Check((x' = 3) => FALSE, "Test 13b failed: false antecedent")
  /\ Check(~((x' = 2) => (x' = 1)), "Test 13c failed: true => false")
  \* 14. CASE
  /\ Check(CASE x' = 1 -> FALSE
             [] x' = 2 -> TRUE
             [] OTHER  -> FALSE, "Test 14a failed: CASE on x'")
  /\ Check((CASE x' > 5 -> 0 [] OTHER -> x') = 2, "Test 14b failed: CASE OTHER x'")
  \* 15. Operator parameters
  /\ Check(Plus(x', x) = 3, "Test 15a failed: Plus(x', x)")
  /\ Check(Twice(x') = 4, "Test 15b failed: Twice(x')")
  /\ Check(InSet(x', {2}), "Test 15c failed: InSet(x', {2})")
  /\ Check(NextVal = 2, "Test 15d failed: NextVal")
  /\ Check(ApplyOp(Inc, x') = 3, "Test 15e failed: ApplyOp(Inc, x')")
  /\ Check(LET L(a) == a + x' IN L(x') = 4, "Test 15f failed: LET operator with x'")

Step ==
  /\ x = 1
  /\ x' = 2
  /\ PrimeTests

Done ==
  /\ x = 2
  /\ UNCHANGED x

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety *)
TypeOK == x \in {1, 2}

(* Liveness: the counter eventually reaches 2 and stays there *)
ReachesTwo == <>(x = 2)
StaysTwo   == <>[](x = 2)
=============================================================================