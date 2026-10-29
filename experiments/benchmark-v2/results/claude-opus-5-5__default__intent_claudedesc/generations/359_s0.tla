------------------------------ MODULE PrimeExpressionTest ------------------------------
(***************************************************************************)
(* Test harness checking that a model checker evaluates expressions       *)
(* containing primed variables correctly in many syntactic contexts.      *)
(*                                                                         *)
(* The behavior has exactly two distinct states:                          *)
(*   Init:      x = 0, z = [i \in {0,1} |-> 0]                            *)
(*   Successor: x = 1, z = [i \in {0,1} |-> 1]                            *)
(* Each step from either state leads to the successor state, so the       *)
(* transition is deterministic. Every test is wrapped in an Assert that   *)
(* fails if a primed expression is evaluated incorrectly.                 *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x, z

vars == <<x, z>>

Dom == {0, 1}

(* Helper definitions used by the tests. *)
f == [i \in Dom |-> i + 1]

Op(a) == a + 1

Op2(a, b) == {a, b}

Init == /\ x = 0
        /\ z = [i \in Dom |-> 0]

(***************************************************************************)
(* The tests. They are evaluated only after x' and z' have been assigned. *)
(***************************************************************************)

\* Conditional expressions (IF-THEN-ELSE)
TestIf ==
    /\ IF x' = 1 THEN TRUE ELSE Assert(FALSE, "Failure: IF-THEN-ELSE with x'")
    /\ Assert((IF x' = 0 THEN 10 ELSE 20) = 20, "Failure: IF value with x'")

\* Equality and inequality comparisons
TestEquality ==
    /\ Assert(x' = 1, "Failure: x' = 1")
    /\ Assert(x' # 0, "Failure: x' # 0")
    /\ Assert(x' # x, "Failure: x' # x")
    /\ Assert(~(x' = 2), "Failure: ~(x' = 2)")
    /\ Assert(z' = [i \in Dom |-> 1], "Failure: z' = function")

\* Set membership and set construction
TestSetMembership ==
    /\ Assert(x' \in {1}, "Failure: x' \\in {1}")
    /\ Assert(x' \notin {0, 2}, "Failure: x' \\notin {0,2}")
    /\ Assert({x'} = {1}, "Failure: {x'} = {1}")
    /\ Assert({x', x} \subseteq Dom, "Failure: {x', x} \\subseteq Dom")
    /\ Assert(<<x', x'>> = <<1, 1>>, "Failure: tuple with x'")

\* Function application and function update
TestFunctions ==
    /\ Assert(f[x'] = 2, "Failure: f[x']")
    /\ Assert(z'[x'] = 1, "Failure: z'[x']")
    /\ Assert(z'[0] = x', "Failure: z'[0] = x'")
    /\ Assert([f EXCEPT ![x'] = 5][1] = 5, "Failure: EXCEPT ![x']")
    /\ Assert([f EXCEPT ![0] = x'][0] = 1, "Failure: EXCEPT ![0] = x'")
    /\ Assert([z' EXCEPT ![x'] = @ + x'][1] = 2, "Failure: EXCEPT on z' with @")
    /\ Assert([i \in {x'} |-> i * 2][1] = 2, "Failure: function constructor over {x'}")

\* Quantified expressions
TestQuantifiers ==
    /\ Assert(\E i \in Dom : i = x', "Failure: \\E with x'")
    /\ Assert(\A i \in {x'} : i = 1, "Failure: \\A over {x'}")
    /\ Assert(\A i \in Dom : z'[i] = x', "Failure: \\A with z' and x'")
    /\ Assert(~\E i \in Dom : z'[i] # x', "Failure: ~\\E with z'")

\* CHOOSE expressions
TestChoose ==
    /\ Assert((CHOOSE i \in Dom : i = x') = 1, "Failure: CHOOSE with x'")
    /\ Assert((CHOOSE i \in {x'} : TRUE) = 1, "Failure: CHOOSE over {x'}")

\* CASE expressions
TestCase ==
    /\ Assert((CASE x' = 1 -> TRUE
                 [] x' = 0 -> FALSE
                 [] OTHER  -> FALSE), "Failure: CASE with x'")
    /\ Assert((CASE x' = 0 -> 0 [] OTHER -> x' + 1) = 2, "Failure: CASE OTHER with x'")

\* Implication expressions
TestImplication ==
    /\ Assert((x' = 1) => (z'[1] = 1), "Failure: x' = 1 => z'[1] = 1")
    /\ Assert((x' = 0) => FALSE, "Failure: x' = 0 => FALSE")
    /\ Assert((x' = 1) <=> (x' # 0), "Failure: <=> with x'")

\* Set operations: SUBSET, UNION, set comprehension
TestSetOps ==
    /\ Assert(SUBSET {x'} = {{}, {1}}, "Failure: SUBSET {x'}")
    /\ Assert(UNION {{x'}, {2}} = {1, 2}, "Failure: UNION with x'")
    /\ Assert({i + x' : i \in Dom} = {1, 2}, "Failure: set map with x'")
    /\ Assert({i \in {0, 1, 2} : i > x'} = {2}, "Failure: set filter with x'")
    /\ Assert({x'} \cup {x} = Dom, "Failure: \\cup with x'")
    /\ Assert({x'} \cap Dom = {1}, "Failure: \\cap with x'")
    /\ Assert(Dom \ {x'} = {0}, "Failure: set difference with x'")

\* Function domain expressions
TestDomain ==
    /\ Assert(DOMAIN [i \in {x'} |-> 0] = {1}, "Failure: DOMAIN over {x'}")
    /\ Assert(DOMAIN z' = Dom, "Failure: DOMAIN z'")
    /\ Assert(x' \in DOMAIN z', "Failure: x' \\in DOMAIN z'")

\* Operator arguments
TestOperatorArgs ==
    /\ Assert(Op(x') = 2, "Failure: Op(x')")
    /\ Assert(Op(z'[x']) = 2, "Failure: Op(z'[x'])")
    /\ Assert(Op2(x', x) = Dom, "Failure: Op2(x', x)")
    /\ Assert(LET y == x' + 1 IN y = 2, "Failure: LET with x'")

AllTests ==
    /\ TestIf
    /\ TestEquality
    /\ TestSetMembership
    /\ TestFunctions
    /\ TestQuantifiers
    /\ TestChoose
    /\ TestCase
    /\ TestImplication
    /\ TestSetOps
    /\ TestDomain
    /\ TestOperatorArgs

(***************************************************************************)
(* Deterministic transition: always moves to x = 1, z = [i |-> 1].        *)
(* The primed variables are assigned first, then all tests are run.       *)
(***************************************************************************)
Next == /\ x' = 1
        /\ z' = [i \in Dom |-> x']
        /\ AllTests

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Properties                                                             *)
(***************************************************************************)

\* Trivially true invariant, ensures the whole state space is processed.
Inv == TRUE

\* Type invariant: only the two expected states are reachable.
TypeOK == /\ x \in Dom
          /\ z \in [Dom -> Dom]
          /\ \A i \in Dom : z[i] = x

\* Exactly two distinct states are reachable.
ReachableStates == \/ (x = 0 /\ z = [i \in Dom |-> 0])
                   \/ (x = 1 /\ z = [i \in Dom |-> 1])

\* Liveness: the successor state is eventually reached and persists.
ReachSuccessor == <>[](x = 1)

=============================================================================