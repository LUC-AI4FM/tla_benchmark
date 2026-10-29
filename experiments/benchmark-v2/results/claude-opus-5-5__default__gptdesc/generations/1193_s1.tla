---------------------------- MODULE PrimedExprTest ----------------------------
(***************************************************************************)
(* Regression-style test for primed expressions in many syntactic         *)
(* contexts: function definitions, set expressions, CHOOSE, function      *)
(* override (EXCEPT), CASE, quantifiers, implication and operator calls.  *)
(* Variables x and y start at 1.  The next-state relation toggles x       *)
(* between 1 and 2 and leaves y unchanged, so exactly two distinct states *)
(* are reachable.  Each context involving x' is checked with Assert, and  *)
(* Print is used to trace the evaluation.                                 *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

TypeOK == /\ x \in {1, 2}
          /\ y = 1

\* Operators used to test operator calls with primed arguments / bodies
Inc(a)      == a + 1
SumPrimed   == x' + y'
IsNext(a)   == a = x'

Init == /\ x = 1
        /\ y = 1

Next ==
  /\ x' = IF x = 1 THEN 2 ELSE 1
  /\ y' = y
  /\ Print(<<"x", x, "x'", x', "y'", y'>>, TRUE)

  \* Function definition whose body refers to x'
  /\ LET f[i \in {1, 2}] == x' + i
     IN  Assert(f[1] = x' + 1 /\ f[2] = x' + 2,
                "Failure: function definition with x'")

  \* Function constructor whose body refers to x'
  /\ LET h == [i \in {1, 2} |-> i * x']
     IN  Assert(h[2] = 2 * x', "Failure: function constructor with x'")

  \* Set expressions
  /\ Assert({x'} \subseteq {1, 2}, "Failure: set enumeration with x'")
  /\ Assert({i \in {1, 2} : i = x'} = {x'},
            "Failure: set filter with x'")
  /\ Assert({i + x' : i \in {0}} = {x'},
            "Failure: set map with x'")
  /\ Assert(x' \in {1, 2} /\ x' \notin {x}, "Failure: membership with x'")

  \* CHOOSE
  /\ Assert((CHOOSE i \in {1, 2} : i = x') = x',
            "Failure: CHOOSE with x'")

  \* Function override (EXCEPT)
  /\ LET g == [i \in {1, 2} |-> 0]
     IN  Assert(/\ [g EXCEPT ![1] = x'][1] = x'
                /\ [g EXCEPT ![2] = @ + x'][2] = x'
                /\ [g EXCEPT ![x'] = 7][x'] = 7,
                "Failure: EXCEPT with x'")

  \* CASE
  /\ Assert(CASE x' = 1 -> x = 2
              [] x' = 2 -> x = 1
              [] OTHER  -> FALSE,
            "Failure: CASE with x'")

  \* IF-THEN-ELSE
  /\ Assert((IF x' = 2 THEN x = 1 ELSE x = 2), "Failure: IF with x'")

  \* Quantifiers
  /\ Assert(\A i \in {x'} : i = x', "Failure: \\A with x'")
  /\ Assert(\E i \in {1, 2} : i = x', "Failure: \\E with x'")
  /\ Assert(\A i \in {1, 2} : (i = x') \/ (i = x),
            "Failure: \\A disjunction with x'")

  \* Implication
  /\ Assert((x' = 2) => (x = 1), "Failure: implication with x' (1)")
  /\ Assert((x' = 1) => (x = 2), "Failure: implication with x' (2)")

  \* Operator calls
  /\ Assert(Inc(x') = x' + 1, "Failure: operator call with x' argument")
  /\ Assert(SumPrimed = x' + 1, "Failure: operator with primed body")
  /\ Assert(IsNext(x'), "Failure: operator comparing to x'")
  /\ Assert(Inc(x)' = x' + 1, "Failure: primed operator application")

  \* LET with primed definitions
  /\ LET nx == x'
     IN  Assert(nx + x = 3, "Failure: LET binding of x'")

Spec == Init /\ [][Next]_vars

\* Safety invariants
TwoStatesOnly == <<x, y>> \in {<<1, 1>>, <<2, 1>>}

YConstant == y = 1

THEOREM Spec => [](TypeOK /\ TwoStatesOnly /\ YConstant)
=============================================================================