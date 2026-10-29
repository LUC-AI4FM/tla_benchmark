---------------------------- MODULE PrimedExprTest ----------------------------
(***************************************************************************)
(* Regression-style test for handling expressions that contain primed     *)
(* variables in actions. A tiny two-variable state machine with x and y.  *)
(* The action TNext sets x' and then checks many syntactic contexts in    *)
(* which x' appears. TLC's Print and Assert operators check that primed   *)
(* expressions are interpreted correctly.                                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC

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
  /\ Print(<<"x' = ", x'>>, TRUE)

  \* Quantifiers
  /\ Assert(\A i \in {x'} : i = 2, "Test 1 (forall) failed")
  /\ Assert(\E i \in {1, x'} : i = 2, "Test 2 (exists) failed")
  /\ Assert(\A i \in {1} : x' = i + 1, "Test 3 (forall body) failed")
  /\ Assert(\E i \in 1..x' : i = x', "Test 4 (exists range) failed")

  \* CHOOSE
  /\ Assert((CHOOSE i \in {x', 5} : i < 3) = 2, "Test 5 (CHOOSE) failed")
  /\ Assert((CHOOSE i \in {1, 2, 3} : i = x') = 2, "Test 6 (CHOOSE body) failed")

  \* Set expressions
  /\ Assert({x'} = {2}, "Test 7 (set enumeration) failed")
  /\ Assert({i \in {1, x'} : i > 1} = {2}, "Test 8 (set filter) failed")
  /\ Assert({x' + i : i \in {1}} = {3}, "Test 9 (set map) failed")
  /\ Assert({i + 1 : i \in {x'}} = {3}, "Test 10 (set map domain) failed")
  /\ Assert(SUBSET {x'} = {{}, {2}}, "Test 11 (SUBSET) failed")
  /\ Assert(UNION {{x'}, {1}} = {1, 2}, "Test 12 (UNION) failed")
  /\ Assert({x'} \cup {1} = {1, 2}, "Test 13 (cup) failed")
  /\ Assert(x' \in 1..3, "Test 14 (in) failed")
  /\ Assert({x'} \X {1} = {<<2, 1>>}, "Test 15 (cartesian) failed")

  \* Function definitions
  /\ Assert(LET f[i \in {1, 2}] == x' + i IN f[1] = 3,
            "Test 16 (recursive-style function def) failed")
  /\ Assert([i \in {1, 2} |-> x' * i][2] = 4, "Test 17 (function constructor) failed")
  /\ Assert([i \in {x'} |-> i][2] = 2, "Test 18 (function domain) failed")
  /\ Assert(LET g == [i \in 1..x' |-> i] IN g[x'] = 2, "Test 19 (LET function) failed")

  \* EXCEPT updates
  /\ Assert([[i \in {1, 2} |-> 0] EXCEPT ![1] = x'][1] = 2, "Test 20 (EXCEPT value) failed")
  /\ Assert([[i \in {1, 2} |-> 0] EXCEPT ![x'] = 7][2] = 7, "Test 21 (EXCEPT index) failed")
  /\ Assert([[i \in {1, 2} |-> x'] EXCEPT ![1] = @ + 1][1] = 3, "Test 22 (EXCEPT @) failed")
  /\ Assert([[a |-> 0, b |-> 0] EXCEPT !.a = x'].a = 2, "Test 23 (record EXCEPT) failed")
  /\ Assert([a |-> x'].a = 2, "Test 24 (record) failed")

  \* Function-set constructors
  /\ Assert([{1} -> {x'}] = {[i \in {1} |-> 2]}, "Test 25 (function set range) failed")
  /\ Assert([{x'} -> {1}] = {[i \in {2} |-> 1]}, "Test 26 (function set domain) failed")
  /\ Assert([a : {x'}] = {[a |-> 2]}, "Test 27 (record set) failed")

  \* Implication
  /\ Assert((x' = 2) => TRUE, "Test 28 (implication lhs) failed")
  /\ Assert(TRUE => (x' = 2), "Test 29 (implication rhs) failed")
  /\ Assert((x' = 3) => FALSE, "Test 30 (implication false lhs) failed")
  /\ Assert((x' = 2) <=> TRUE, "Test 31 (equivalence) failed")

  \* IF / CASE
  /\ Assert(IF x' = 2 THEN TRUE ELSE FALSE, "Test 32 (IF) failed")
  /\ Assert(CASE x' = 2 -> TRUE [] OTHER -> FALSE, "Test 33 (CASE guard) failed")
  /\ Assert((CASE x = 1 -> x' [] OTHER -> 0) = 2, "Test 34 (CASE value) failed")

  \* DOMAIN
  /\ Assert(DOMAIN [i \in {x'} |-> i] = {2}, "Test 35 (DOMAIN) failed")
  /\ Assert(DOMAIN <<x', x'>> = {1, 2}, "Test 36 (DOMAIN tuple) failed")
  /\ Assert(Len(<<x', y'>>) = 2, "Test 37 (Len) failed")

  \* Operator application
  /\ Assert(Op(x') = 3, "Test 38 (operator application) failed")
  /\ Assert(Op2(x', y') = {1, 2}, "Test 39 (binary operator application) failed")
  /\ Assert(LET h(a) == a + x' IN h(1) = 3, "Test 40 (LET operator) failed")
  /\ Assert(x' + y' = 3, "Test 41 (arithmetic) failed")
  /\ Assert(<<x, y>>' = <<2, 1>>, "Test 42 (primed tuple) failed")

Next == TNext \/ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_vars
=============================================================================