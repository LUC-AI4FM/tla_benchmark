---------------------------- MODULE PrimedExprTest ----------------------------
(***************************************************************************)
(* Regression-style test of expressions containing primed variables in    *)
(* actions.  A tiny two-variable state machine with variables x and y,    *)
(* both initialized to 1.  The action TNext sets x' and then checks that  *)
(* x' is interpreted correctly in many syntactic contexts: quantifiers,   *)
(* CHOOSE, set expressions, function definitions, EXCEPT, function-set    *)
(* constructors, implication, CASE, DOMAIN and operator application.      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

Init == /\ x = 1
        /\ y = 1

Foo(a) == a + 1

Bar(a, b) == a * b

TNext ==
  /\ x' = 2
  /\ y' = y
  /\ Print(<<"x' =", x'>>, TRUE)
  \* Universal and existential quantifiers
  /\ Assert(\A i \in {x'} : i = 2,
            "Failed: x' in \\A")
  /\ Assert(\E i \in {1, x'} : i = 2,
            "Failed: x' in \\E")
  /\ Assert(\A i \in 1..x' : i \leq 2,
            "Failed: x' in \\A bound")
  \* CHOOSE
  /\ Assert((CHOOSE i \in {x'} : TRUE) = 2,
            "Failed: x' in CHOOSE bound")
  /\ Assert((CHOOSE i \in 1..5 : i = x') = 2,
            "Failed: x' in CHOOSE body")
  \* Set expressions
  /\ Assert({x'} = {2},
            "Failed: x' in set enumeration")
  /\ Assert({i \in 1..x' : i > 1} = {2},
            "Failed: x' in set filter")
  /\ Assert({i + x' : i \in {0, 1}} = {2, 3},
            "Failed: x' in set map")
  /\ Assert(x' \in 1..3,
            "Failed: x' in set membership")
  /\ Assert(Cardinality(1..x') = 2,
            "Failed: x' in Cardinality")
  \* Function definitions
  /\ Assert(LET f[i \in 1..x'] == i + x' IN f[1] = 3,
            "Failed: x' in recursive-style function definition")
  /\ Assert([i \in {1} |-> x'][1] = 2,
            "Failed: x' in function constructor")
  /\ Assert([i \in 1..x' |-> i * x'][2] = 4,
            "Failed: x' in function constructor domain")
  \* EXCEPT
  /\ Assert([[i \in 1..2 |-> 0] EXCEPT ![x'] = x'] = <<0, 2>>,
            "Failed: x' in EXCEPT")
  /\ Assert([[i \in 1..2 |-> 1] EXCEPT ![1] = @ + x'] = <<3, 1>>,
            "Failed: x' in EXCEPT with @")
  /\ Assert([[a |-> 0] EXCEPT !.a = x'].a = 2,
            "Failed: x' in record EXCEPT")
  \* Function sets and record sets
  /\ Assert([{1} -> {x'}] = {[i \in {1} |-> 2]},
            "Failed: x' in function set")
  /\ Assert([a : {x'}] = {[a |-> 2]},
            "Failed: x' in record set")
  /\ Assert([a |-> x'].a = 2,
            "Failed: x' in record constructor")
  \* Implication
  /\ Assert((x' = 2) => (y' = 1),
            "Failed: x' in implication")
  /\ Assert((x' = 1) => FALSE,
            "Failed: x' in implication antecedent")
  \* IF / CASE
  /\ Assert(IF x' = 2 THEN TRUE ELSE FALSE,
            "Failed: x' in IF")
  /\ Assert(CASE x' = 1 -> FALSE
              [] x' = 2 -> TRUE
              [] OTHER  -> FALSE,
            "Failed: x' in CASE")
  \* DOMAIN
  /\ Assert(DOMAIN [i \in 1..x' |-> i] = 1..2,
            "Failed: x' in DOMAIN")
  /\ Assert(DOMAIN <<x', x'>> = 1..2,
            "Failed: x' in DOMAIN of tuple")
  \* Operator application
  /\ Assert(Foo(x') = 3,
            "Failed: x' in operator application")
  /\ Assert(Bar(x', x') = 4,
            "Failed: x' in binary operator application")
  /\ Assert(Len(<<x', y'>>) = 2,
            "Failed: x' in Len")
  \* LET
  /\ Assert(LET z == x' + 1 IN z = 3,
            "Failed: x' in LET")
  \* Tuples / primed tuples
  /\ Assert(<<x, y>>' = <<2, 1>>,
            "Failed: primed tuple")
  /\ Assert((x + y)' = 3,
            "Failed: primed expression")

Next == TNext \/ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_vars

TypeOK == /\ x \in {1, 2}
          /\ y = 1

=============================================================================