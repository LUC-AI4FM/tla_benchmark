------------------------------ MODULE PrimedExprTest ------------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

TypeOK == /\ x \in {1, 2}
          /\ y \in {1}

Init == /\ x = 1
        /\ y = 1

\* Operator that takes an argument; it is called with a primed expression.
Inc(a) == a + 1

\* Operator whose body refers directly to a primed variable.
XPrimePlus(a) == x' + a

\* Function definitions whose bodies contain x'.
F == [i \in {1, 2} |-> i + x']

G[i \in {1, 2}] == IF i = 1 THEN x' ELSE x' * 2

\* Set expressions containing x'.
S1 == {x'}
S2 == {i \in {1, 2, 3} : i = x'}
S3 == {i + x' : i \in {0, 1}}

Next ==
  /\ x' = 2
  /\ y' = y
  /\ Print(<<"x' =", x'>>, TRUE)
  \* Function definitions
  /\ Assert(F[1] = 3 /\ F[2] = 4, "Test 1 failed: function constructor with x'")
  /\ Assert(G[1] = 2 /\ G[2] = 4, "Test 2 failed: recursive-style function def with x'")
  \* Set expressions
  /\ Assert(S1 = {2}, "Test 3 failed: set enumeration with x'")
  /\ Assert(S2 = {2}, "Test 4 failed: set filter with x'")
  /\ Assert(S3 = {2, 3}, "Test 5 failed: set map with x'")
  /\ Assert(x' \in {1, 2}, "Test 6 failed: membership with x'")
  \* CHOOSE
  /\ Assert((CHOOSE i \in {1, 2, 3} : i = x') = 2, "Test 7 failed: CHOOSE with x'")
  \* Function override (EXCEPT)
  /\ Assert([F EXCEPT ![1] = x' + 10][1] = 12, "Test 8 failed: EXCEPT with x'")
  /\ Assert([F EXCEPT ![x'] = @ + x'][2] = 6, "Test 9 failed: EXCEPT index x'")
  \* CASE
  /\ Assert((CASE x' = 1 -> FALSE
               [] x' = 2 -> TRUE
               [] OTHER  -> FALSE), "Test 10 failed: CASE with x'")
  \* Quantifiers
  /\ Assert(\A i \in {x'} : i = 2, "Test 11 failed: \\A with x'")
  /\ Assert(\E i \in {1, 2, 3} : i = x', "Test 12 failed: \\E with x'")
  /\ Assert(\A i \in {1} : i + x' = 3, "Test 13 failed: \\A body with x'")
  \* Implication
  /\ Assert((x' = 2) => (y' = 1), "Test 14 failed: implication with x'")
  /\ Assert((x' = 1) => FALSE, "Test 15 failed: false antecedent with x'")
  \* LET / IF
  /\ Assert(LET z == x' IN z + 1 = 3, "Test 16 failed: LET with x'")
  /\ Assert(IF x' = 2 THEN TRUE ELSE FALSE, "Test 17 failed: IF with x'")
  \* Operator calls
  /\ Assert(Inc(x') = 3, "Test 18 failed: operator call with argument x'")
  /\ Assert(XPrimePlus(1) = 3, "Test 19 failed: operator body with x'")
  /\ Assert(Inc(x)' = 3, "Test 20 failed: primed operator call")

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: only the two states (x=1,y=1) and (x=2,y=1) are reachable.
Inv == TypeOK /\ y = 1

\* Liveness: x eventually becomes 2 and stays there.
Liveness == <>[](x = 2)

==================================================================================