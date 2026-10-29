------------------------------- MODULE PrimedExprTest -------------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
  /\ x = 1
  /\ y = 1

\* Operator used to test passing a primed expression as an argument
Inc(a) == a + 1

\* Operator whose body refers to x' directly
XPrimeIsTwo == x' = 2

Next ==
  /\ x' = 2
  /\ y' = y
  \* Function definition involving x'
  /\ LET f[i \in {1, 2}] == x' + i
     IN  Assert(f[1] = 3 /\ f[2] = 4, "Failure: function definition with x'")
  \* Function constructor involving x'
  /\ LET g == [i \in {1, 2} |-> x']
     IN  Assert(g[1] = 2 /\ g[2] = 2, "Failure: function constructor with x'")
  \* Set expressions involving x'
  /\ Assert({x'} = {2}, "Failure: set enumeration with x'")
  /\ Assert({i \in {1, 2, 3} : i = x'} = {2}, "Failure: set filter with x'")
  /\ Assert({i + x' : i \in {0, 1}} = {2, 3}, "Failure: set map with x'")
  /\ Assert(x' \in {1, 2}, "Failure: set membership with x'")
  \* CHOOSE involving x'
  /\ Assert((CHOOSE i \in {1, 2, 3} : i = x') = 2, "Failure: CHOOSE with x'")
  \* Function override (EXCEPT) involving x'
  /\ LET h == [i \in {1, 2} |-> 0]
     IN  Assert([h EXCEPT ![1] = x'][1] = 2, "Failure: EXCEPT with x'")
  /\ LET h2 == [i \in {1, 2} |-> i]
     IN  Assert([h2 EXCEPT ![x'] = @ + x'][2] = 4, "Failure: EXCEPT index with x'")
  \* CASE involving x'
  /\ Assert(CASE x' = 1 -> FALSE
              [] x' = 2 -> TRUE
              [] OTHER  -> FALSE, "Failure: CASE with x'")
  \* IF-THEN-ELSE involving x'
  /\ Assert(IF x' = 2 THEN TRUE ELSE FALSE, "Failure: IF with x'")
  \* Quantifiers involving x'
  /\ Assert(\A i \in {x'} : i = 2, "Failure: forall with x'")
  /\ Assert(\E i \in {1, 2, 3} : i = x', "Failure: exists with x'")
  /\ Assert(\A i \in {1, 2} : i <= x', "Failure: forall body with x'")
  \* Implication involving x'
  /\ Assert((x' = 2) => (y' = 1), "Failure: implication with x'")
  /\ Assert((x' = 1) => FALSE, "Failure: implication false antecedent with x'")
  \* Operator calls involving x'
  /\ Assert(Inc(x') = 3, "Failure: operator call with x'")
  /\ Assert(XPrimeIsTwo, "Failure: operator body with x'")
  \* Tuples and records involving x'
  /\ Assert(<<x', y'>> = <<2, 1>>, "Failure: tuple with x'")
  /\ Assert([a |-> x'].a = 2, "Failure: record with x'")
  /\ PrintT(<<"x, x'", x, x'>>)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ x \in {1, 2}
  /\ y = 1

=====================================================================================