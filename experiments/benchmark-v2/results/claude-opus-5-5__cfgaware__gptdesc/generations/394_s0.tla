---------------------------- MODULE PrimeSemantics ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

\* Helper operators used to test priming of operator applications
Foo(a) == a + 1
Bar == x
Baz == x + y
Choose(c, a, b) == IF c THEN a ELSE b

Init ==
    /\ x = 0
    /\ y = 0

Next ==
    \* First assign primed variables
    /\ x' = (x + 1) % 3
    /\ y' = x
    \* Priming a direct variable reference
    /\ Assert(x' = (x + 1) % 3, "direct variable priming failed")
    \* Priming a zero-arity operator: Bar' means x'
    /\ Assert(Bar' = x', "priming of Bar should equal x'")
    \* Priming an operator application: Foo(x)' = Foo(x') = x' + 1
    /\ Assert(Foo(x)' = x' + 1, "priming of Foo(x) failed")
    /\ Assert((Foo(x))' = Foo(x'), "Foo(x)' should equal Foo(x')")
    \* Priming an operator mentioning several variables
    /\ Assert(Baz' = x' + y', "priming of Baz failed")
    \* A LET-bound name is not a variable: z' means (x)' = x'
    /\ LET z == x
           w == x'
           u == Foo(y)
       IN /\ Assert(z = x, "unprimed LET name should equal x")
          /\ Assert(z' = x', "primed LET name should equal x'")
          /\ Assert(w = x', "LET name defined as x' should equal x'")
          /\ Assert(u' = y' + 1, "primed LET operator call failed")
    \* Priming a whole LET expression
    /\ Assert((LET v == x IN v + 1)' = x' + 1, "priming a LET expression failed")
    \* Priming a conditional: the condition is primed too
    /\ Assert((IF x = 0 THEN y ELSE x)' = (IF x' = 0 THEN y' ELSE x'),
              "priming of IF-THEN-ELSE failed")
    /\ Assert(Choose(x = 0, y, x)' = Choose(x' = 0, y', x'),
              "priming of conditional operator failed")
    /\ PrintT(<<"x", x, "x'", x', "y", y, "y'", y'>>)

Spec == Init /\ [][Next]_vars

Inv == TRUE

=============================================================================