---------------------------- MODULE PrimeTest ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Dom == {1, 2}

Op(a) == a + 1

Op2(a, b) == a + b

Init ==
    /\ x = 0
    /\ y = [i \in Dom |-> 0]

Step ==
    /\ x = 0
    /\ x' = 1
    /\ y' = [y EXCEPT ![1] = 1]
    \* Conditional expressions
    /\ Assert(IF x' = 1 THEN TRUE ELSE FALSE, "Failure: IF with x' in condition")
    /\ Assert((IF x' > 0 THEN x' ELSE 0) = 1, "Failure: IF with x' in branches")
    \* Equality and inequality
    /\ Assert(x' = 1, "Failure: x' = 1")
    /\ Assert(x' # x, "Failure: x' # x")
    /\ Assert(~(x' = 0), "Failure: ~(x' = 0)")
    /\ Assert((x + 1)' = 2, "Failure: (x + 1)' = 2")
    \* Set membership and construction
    /\ Assert(x' \in {1}, "Failure: x' \\in {1}")
    /\ Assert(x' \notin {0}, "Failure: x' \\notin {0}")
    /\ Assert({x'} = {1}, "Failure: {x'} = {1}")
    /\ Assert({x', x} = {0, 1}, "Failure: {x', x} = {0, 1}")
    \* Function application and update
    /\ Assert(y'[1] = 1, "Failure: y'[1] = 1")
    /\ Assert(y'[2] = 0, "Failure: y'[2] = 0")
    /\ Assert(y[x'] = 0, "Failure: y[x'] = 0")
    /\ Assert(y'[x'] = 1, "Failure: y'[x'] = 1")
    /\ Assert([y' EXCEPT ![2] = x'] = [i \in Dom |-> 1], "Failure: EXCEPT on y'")
    /\ Assert([y EXCEPT ![2] = x'][2] = 1, "Failure: EXCEPT with x' value")
    /\ Assert([i \in Dom |-> x'] = [i \in Dom |-> 1], "Failure: function constructor with x'")
    \* Quantified expressions
    /\ Assert(\E i \in DOMAIN y' : y'[i] = x', "Failure: \\E with primes")
    /\ Assert(\A i \in {x'} : i = 1, "Failure: \\A over {x'}")
    /\ Assert(\A i \in Dom : y'[i] \in {0, x'}, "Failure: \\A with y'")
    /\ Assert(~\E i \in Dom : y'[i] > x', "Failure: ~\\E with primes")
    \* CHOOSE expressions
    /\ Assert((CHOOSE i \in {x', x + 5} : i < 3) = 1, "Failure: CHOOSE with x'")
    /\ Assert((CHOOSE i \in Dom : y'[i] = 1) = 1, "Failure: CHOOSE with y'")
    \* CASE expressions
    /\ Assert(CASE x' = 1 -> TRUE [] OTHER -> FALSE, "Failure: CASE with x'")
    /\ Assert((CASE x' = 0 -> 10 [] x' = 1 -> 20 [] OTHER -> 30) = 20, "Failure: CASE value")
    \* Implication
    /\ Assert((x' = 1) => (y'[1] = 1), "Failure: implication with primes")
    /\ Assert((x' = 0) => FALSE, "Failure: vacuous implication with x'")
    \* Set operations
    /\ Assert(SUBSET {x'} = {{}, {1}}, "Failure: SUBSET {x'}")
    /\ Assert(UNION {{x'}, {x}} = {0, 1}, "Failure: UNION with x'")
    /\ Assert({i + x' : i \in {0, 1}} = {1, 2}, "Failure: set map with x'")
    /\ Assert({i \in {0, 1, 2} : i = x'} = {1}, "Failure: set filter with x'")
    /\ Assert({x'} \cup {x} = {0, 1}, "Failure: \\cup with x'")
    /\ Assert({x'} \cap {x} = {}, "Failure: \\cap with x'")
    \* Function domain
    /\ Assert(DOMAIN y' = Dom, "Failure: DOMAIN y'")
    /\ Assert(DOMAIN [i \in {x'} |-> i] = {1}, "Failure: DOMAIN of function over {x'}")
    \* Operator arguments
    /\ Assert(Op(x') = 2, "Failure: Op(x')")
    /\ Assert(Op2(x', y'[1]) = 2, "Failure: Op2(x', y'[1])")
    /\ Assert(LET z == x' IN z + 1 = 2, "Failure: LET with x'")

Stutter ==
    /\ x = 1
    /\ UNCHANGED vars

Next == Step \/ Stutter

Spec == Init /\ [][Next]_vars

Inv == TRUE

=============================================================================