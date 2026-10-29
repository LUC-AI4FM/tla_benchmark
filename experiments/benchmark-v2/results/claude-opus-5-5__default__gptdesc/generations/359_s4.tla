------------------------------- MODULE PrimedExprTest -------------------------------
(***************************************************************************)
(* Regression-style test for expressions containing primed variables in    *)
(* actions.  A tiny two-variable state machine: x and y both start at 1.   *)
(* The action TNext sets x' and then checks many syntactic contexts in     *)
(* which x' appears.  TLC's Print and Assert operators check that the      *)
(* primed expressions are interpreted correctly.                           *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Op(a) == a + 1

Op2(a, b) == {a, b}

Init ==
  /\ x = 1
  /\ y = 1

TNext ==
  /\ x' = 2
  /\ y' = y
  \* Universal and existential quantifiers
  /\ Assert(\A i \in {x'} : i = 2, "Failed: \\A with x'")
  /\ Assert(\E i \in {x', 5} : i = 2, "Failed: \\E with x'")
  /\ Assert(\A i \in {1} : x' = i + 1, "Failed: x' in \\A body")
  /\ Assert(\E i \in {1, 2, 3} : i = x', "Failed: x' in \\E body")
  \* CHOOSE
  /\ Assert((CHOOSE i \in {x', 7} : i < 5) = 2, "Failed: CHOOSE with x'")
  /\ Assert((CHOOSE i \in {1, 2, 3} : i = x') = 2, "Failed: x' in CHOOSE body")
  \* Set expressions
  /\ Assert({x'} = {2}, "Failed: set enumeration with x'")
  /\ Assert({i \in {1, 2, 3} : i = x'} = {2}, "Failed: set filter with x'")
  /\ Assert({i + x' : i \in {1}} = {3}, "Failed: set map with x'")
  /\ Assert(x' \in {1, 2}, "Failed: membership with x'")
  /\ Assert({x'} \cup {y'} = {1, 2}, "Failed: union with x'")
  /\ Assert(SUBSET {x'} = {{}, {2}}, "Failed: SUBSET with x'")
  \* Function definitions and applications
  /\ Assert([i \in {1} |-> x'][1] = 2, "Failed: function constructor with x'")
  /\ Assert([i \in {x'} |-> i + 1][2] = 3, "Failed: function domain with x'")
  /\ Assert(LET f[i \in {x'}] == i + x' IN f[2] = 4,
            "Failed: recursive-style function definition with x'")
  /\ Assert(LET g(a) == a + x' IN g(1) = 3, "Failed: LET operator with x'")
  \* EXCEPT
  /\ Assert([[i \in {1, 2} |-> 0] EXCEPT ![1] = x'][1] = 2,
            "Failed: EXCEPT value with x'")
  /\ Assert([[i \in {1, 2} |-> 0] EXCEPT ![x'] = 7][2] = 7,
            "Failed: EXCEPT index with x'")
  /\ Assert([[i \in {1, 2} |-> 1] EXCEPT ![1] = @ + x'][1] = 3,
            "Failed: EXCEPT @ with x'")
  \* Records
  /\ Assert([a |-> x', b |-> y'].a = 2, "Failed: record with x'")
  \* Function-set constructor
  /\ Assert([{1} -> {x'}] = {[i \in {1} |-> 2]}, "Failed: function set with x'")
  /\ Assert([{x'} -> {0}] = {[i \in {2} |-> 0]}, "Failed: function set domain with x'")
  \* Implication
  /\ Assert((x' = 2) => (y' = 1), "Failed: implication with x'")
  /\ Assert((x' = 3) => FALSE, "Failed: vacuous implication with x'")
  \* CASE
  /\ Assert((CASE x' = 1 -> FALSE
               [] x' = 2 -> TRUE
               [] OTHER  -> FALSE), "Failed: CASE with x'")
  \* IF-THEN-ELSE
  /\ Assert(IF x' = 2 THEN TRUE ELSE FALSE, "Failed: IF with x'")
  \* DOMAIN
  /\ Assert(DOMAIN [i \in {x'} |-> 0] = {2}, "Failed: DOMAIN with x'")
  \* Operator application
  /\ Assert(Op(x') = 3, "Failed: operator application with x'")
  /\ Assert(Op2(x', y') = {1, 2}, "Failed: binary operator application with x'")
  /\ Assert(Op(x)' = 3, "Failed: primed operator application")
  \* Tuples
  /\ Assert(<<x', y'>> = <<2, 1>>, "Failed: tuple with x'")
  /\ Assert(<<x, y>>' = <<2, 1>>, "Failed: primed tuple")
  \* Print
  /\ Print(<<"x' =", x', "y' =", y'>>, TRUE)

Next == TNext \/ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ x \in {1, 2}
  /\ y = 1
=====================================================================================