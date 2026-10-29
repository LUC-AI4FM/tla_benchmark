---------------------------- MODULE PrimedExprTest ----------------------------
(***************************************************************************)
(* Regression-style test of primed expressions in many syntactic contexts *)
(* within the next-state relation. Two variables, x and y, both start at  *)
(* 1. Only x changes, so exactly two distinct states are reachable:       *)
(* (x=1, y=1) and (x=2, y=1).                                              *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = 1
    /\ y = 1
    /\ Print(<<"Init", x, y>>, TRUE)

(* Operators used to test priming through operator calls *)
Plus(a, b) == a + b

AddY(a) == a + y

XPrimePlusOne == x' + 1

IsNextX(v) == v = x'

Next ==
    /\ x' = IF x = 1 THEN 2 ELSE 1
    /\ y' = y

    \* Function definition containing a primed expression
    /\ LET f[i \in {1, 2}] == x' + i
       IN  Assert(f[1] = x' + 1 /\ f[2] = x' + 2,
                  "Failure: function definition with x'")

    \* Function constructor containing a primed expression
    /\ LET g == [i \in {1, 2} |-> i * x']
       IN  Assert(g[2] = 2 * x', "Failure: function constructor with x'")

    \* Set enumeration
    /\ Assert({x'} = {3 - x}, "Failure: set enumeration with x'")

    \* Set filter
    /\ Assert({i \in {1, 2, 3} : i = x'} = {x'},
              "Failure: set filter with x'")

    \* Set map
    /\ Assert({i + x' : i \in {0}} = {x'},
              "Failure: set map with x'")

    \* Set membership / SUBSET
    /\ Assert(x' \in {1, 2} /\ {x'} \in SUBSET {1, 2},
              "Failure: membership with x'")

    \* CHOOSE
    /\ Assert((CHOOSE i \in {1, 2} : i = x') = x',
              "Failure: CHOOSE with x'")

    \* Function override (EXCEPT)
    /\ Assert([[i \in {1, 2} |-> 0] EXCEPT ![x'] = x'][x'] = x',
              "Failure: EXCEPT with x'")
    /\ Assert([[i \in {1, 2} |-> i] EXCEPT ![1] = @ + x'][1] = 1 + x',
              "Failure: EXCEPT with @ and x'")

    \* CASE
    /\ Assert(CASE x' = 1 -> x = 2
                [] x' = 2 -> x = 1
                [] OTHER  -> FALSE,
              "Failure: CASE with x'")

    \* IF-THEN-ELSE
    /\ Assert((IF x' = 2 THEN 1 ELSE 2) = x,
              "Failure: IF with x'")

    \* Existential quantifier
    /\ Assert(\E i \in {1, 2} : i = x',
              "Failure: \\E with x'")

    \* Universal quantifier
    /\ Assert(\A i \in {x'} : i = x',
              "Failure: \\A with x'")
    /\ Assert(\A i \in {1, 2} : (i = x') \/ (i = x),
              "Failure: \\A over domain with x'")

    \* Implication
    /\ Assert((x' = 2) => (x = 1), "Failure: implication with x' (1)")
    /\ Assert((x' = 1) => (x = 2), "Failure: implication with x' (2)")

    \* Equivalence
    /\ Assert((x' = 2) <=> (x = 1), "Failure: equivalence with x'")

    \* Operator calls with primed arguments and primes in bodies
    /\ Assert(Plus(x', y') = x' + y, "Failure: operator call Plus(x', y')")
    /\ Assert(AddY(x') = x' + 1, "Failure: operator call AddY(x')")
    /\ Assert(XPrimePlusOne = x' + 1, "Failure: operator XPrimePlusOne")
    /\ Assert(IsNextX(3 - x), "Failure: operator IsNextX")

    \* Primed parenthesized expressions
    /\ Assert((x + y)' = x' + y', "Failure: (x + y)'")
    /\ Assert(<<x, y>>' = <<x', y'>>, "Failure: <<x, y>>'")

    \* Tuples and records
    /\ Assert(<<x', y'>>[1] = x', "Failure: tuple with x'")
    /\ Assert([a |-> x', b |-> y'].a = x', "Failure: record with x'")

    /\ Print(<<"Next", x, y, "->", x', y'>>, TRUE)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ x \in {1, 2}
    /\ y = 1

YConstant == y = 1

(* Action property: every step flips x and leaves y unchanged *)
StepOK == [][x' = 3 - x /\ y' = y]_vars

(* Liveness: x keeps alternating between 1 and 2 *)
XReachesTwo == []<>(x = 2)
XReachesOne == []<>(x = 1)

=============================================================================