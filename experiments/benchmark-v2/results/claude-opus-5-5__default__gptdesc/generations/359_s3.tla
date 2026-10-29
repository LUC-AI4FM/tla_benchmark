---------------------------- MODULE PrimedExprs ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

Init == /\ x = 1
        /\ y = 1

Op(a) == a + 1

Op2(a, b) == {a, b}

TNext ==
  /\ x' = IF x = 1 THEN 2 ELSE 1
  /\ UNCHANGED y
  \* Quantifiers
  /\ Assert(\A i \in {x'} : i = x', "Failure: bounded \\A with x'")
  /\ Assert(\E i \in {x, x'} : i = x', "Failure: bounded \\E with x'")
  /\ \A i \in {x'} : i = x'
  /\ \E i \in {x', x} : i = x'
  \* CHOOSE
  /\ Assert((CHOOSE i \in {x'} : TRUE) = x', "Failure: CHOOSE with x'")
  /\ Assert((CHOOSE i \in {1, 2} : i = x') = x', "Failure: CHOOSE pred with x'")
  \* Set expressions
  /\ Assert({i \in {x', x} : i = x'} = {x'}, "Failure: set filter with x'")
  /\ Assert({i + 0 : i \in {x'}} = {x'}, "Failure: set map with x'")
  /\ Assert(x' \in {x'} \cup {x}, "Failure: set union with x'")
  /\ Assert(SUBSET {x'} = {{}, {x'}}, "Failure: SUBSET with x'")
  /\ Assert(UNION {{x'}, {x'}} = {x'}, "Failure: UNION with x'")
  /\ Assert(Cardinality({x'}) = 1, "Failure: Cardinality with x'")
  \* Function definitions
  /\ Assert(LET f[i \in {x'}] == i + x'
            IN  f[x'] = 2 * x', "Failure: LET function def with x'")
  /\ Assert([i \in {1, 2} |-> x'][1] = x', "Failure: function constructor with x'")
  /\ Assert([i \in {x'} |-> i][x'] = x', "Failure: function domain with x'")
  \* EXCEPT
  /\ Assert([[i \in {1, 2} |-> 0] EXCEPT ![1] = x'][1] = x',
            "Failure: EXCEPT value with x'")
  /\ Assert([[i \in {1, 2} |-> 0] EXCEPT ![x'] = 7][x'] = 7,
            "Failure: EXCEPT index with x'")
  /\ Assert([[i \in {1, 2} |-> x'] EXCEPT ![1] = @ + x'][1] = 2 * x',
            "Failure: EXCEPT @ with x'")
  /\ Assert([[a |-> 0] EXCEPT !.a = x'].a = x', "Failure: record EXCEPT with x'")
  \* Function-set constructors
  /\ Assert([{x'} -> {x'}] = {[i \in {x'} |-> x']}, "Failure: function set with x'")
  /\ Assert([a : {x'}] = {[a |-> x']}, "Failure: record set with x'")
  /\ Assert([a |-> x'].a = x', "Failure: record with x'")
  /\ Assert(<<x', x>>[1] = x', "Failure: tuple with x'")
  \* Implication
  /\ Assert((x' = 2) => (x = 1), "Failure: implication with x'")
  /\ (x' = 1) => (x = 2)
  /\ Assert((x = 1) <=> (x' = 2), "Failure: equivalence with x'")
  \* CASE
  /\ Assert((CASE x' = 1 -> TRUE
             []   x' = 2 -> TRUE
             []   OTHER  -> FALSE), "Failure: CASE with x'")
  /\ (CASE x' = 1 -> x = 2
      []   OTHER  -> x = 1)
  \* IF-THEN-ELSE
  /\ Assert(IF x' = 2 THEN x = 1 ELSE x = 2, "Failure: IF with x'")
  \* DOMAIN
  /\ Assert(DOMAIN [i \in {x'} |-> 0] = {x'}, "Failure: DOMAIN with x'")
  /\ Assert(DOMAIN <<x', x'>> = {1, 2}, "Failure: DOMAIN tuple with x'")
  \* Operator application
  /\ Assert(Op(x') = x' + 1, "Failure: operator application with x'")
  /\ Assert(Op2(x', x') = {x'}, "Failure: operator application (2 args) with x'")
  /\ Assert(LET g(a) == a * x' IN g(1) = x', "Failure: LET operator with x'")
  \* Priming of compound expressions
  /\ Assert((x + y)' = x' + y, "Failure: primed compound expression")
  /\ Assert(<<x, y>>' = <<x', y>>, "Failure: primed tuple")
  /\ Print(<<"x' =", x', "y' =", y'>>, TRUE)

Next == TNext \/ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_vars

TypeOK == /\ x \in {1, 2}
          /\ y = 1

=============================================================================