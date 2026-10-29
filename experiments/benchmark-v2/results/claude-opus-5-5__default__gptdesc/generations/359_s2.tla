---------------------------- MODULE PrimedExprTest ----------------------------
(***************************************************************************)
(* Regression-style test for expressions containing primed variables in   *)
(* actions.  TNext sets x' and then checks that x' is evaluated correctly  *)
(* in many syntactic contexts: quantifiers, CHOOSE, set expressions,       *)
(* function definitions, EXCEPT, function-set constructors, implication,  *)
(* CASE, DOMAIN and operator application.                                  *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init == /\ x = 1
        /\ y = 1

Inc(a) == a + 1

TNext ==
  /\ x' = 2
  /\ y' = y
  \* Universal quantifier
  /\ Assert(\A i \in {x'} : i = 2, "Failed: \\A with primed variable")
  \* Existential quantifier
  /\ Assert(\E i \in {x', 3} : i = 2, "Failed: \\E with primed variable")
  \* Quantifier with x' in body
  /\ Assert(\A i \in {1} : x' = i + 1, "Failed: x' in quantifier body")
  \* CHOOSE
  /\ Assert((CHOOSE i \in {x', 3} : i < 3) = 2, "Failed: CHOOSE with x'")
  /\ Assert((CHOOSE i \in {1, 2, 3} : i = x') = 2, "Failed: x' in CHOOSE body")
  \* Set enumeration
  /\ Assert({x', 3} = {2, 3}, "Failed: set enumeration with x'")
  \* Set filter (subset)
  /\ Assert({i \in {x', 3, 4} : i > 2} = {3, 4}, "Failed: set filter with x'")
  /\ Assert({i \in {1, 2, 3} : i = x'} = {2}, "Failed: x' in set filter predicate")
  \* Set map (image)
  /\ Assert({x' + i : i \in {1, 2}} = {3, 4}, "Failed: set map with x'")
  \* Function definition
  /\ Assert(LET f[i \in {1, 2}] == x' + i IN f[1] = 3,
            "Failed: function definition with x'")
  /\ Assert([i \in {x'} |-> i * 2][2] = 4, "Failed: function constructor with x'")
  \* EXCEPT
  /\ Assert([[i \in {1, 2} |-> i] EXCEPT ![1] = x'][1] = 2,
            "Failed: EXCEPT with x' as new value")
  /\ Assert([[i \in {1, 2} |-> i] EXCEPT ![x'] = 7][2] = 7,
            "Failed: EXCEPT with x' as index")
  /\ Assert([[i \in {1, 2} |-> i] EXCEPT ![1] = @ + x'][1] = 3,
            "Failed: EXCEPT with @ and x'")
  \* Function-set constructor
  /\ Assert([{1} -> {x'}] = {[i \in {1} |-> 2]},
            "Failed: function set with x'")
  /\ Assert([{x'} -> {1}] = {[i \in {2} |-> 1]},
            "Failed: function set domain with x'")
  \* Implication
  /\ Assert((x' = 2) => TRUE, "Failed: implication with x'")
  /\ Assert(~((x' = 2) => FALSE), "Failed: implication antecedent with x'")
  \* CASE
  /\ Assert(CASE x' = 1 -> FALSE
              [] x' = 2 -> TRUE
              [] OTHER  -> FALSE,
            "Failed: CASE with x'")
  /\ Assert((CASE x' = 2 -> x' + 1 [] OTHER -> 0) = 3,
            "Failed: CASE arm value with x'")
  \* IF-THEN-ELSE
  /\ Assert(IF x' = 2 THEN TRUE ELSE FALSE, "Failed: IF with x'")
  \* DOMAIN
  /\ Assert(DOMAIN [i \in {x'} |-> i] = {2}, "Failed: DOMAIN with x'")
  \* Operator application
  /\ Assert(Inc(x') = 3, "Failed: operator application with x'")
  /\ Assert(LET g(a) == a + x' IN g(1) = 3, "Failed: LET operator with x'")
  \* Tuples and records
  /\ Assert(<<x', y'>> = <<2, 1>>, "Failed: tuple with primes")
  /\ Assert([a |-> x'].a = 2, "Failed: record with x'")
  \* Primed tuple
  /\ Assert(<<x, y>>' = <<2, 1>>, "Failed: primed tuple")
  /\ Print(<<"TNext checks passed, x' =", x'>>, TRUE)

Next == TNext \/ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_vars

TypeOK == /\ x \in {1, 2}
          /\ y = 1
===============================================================================