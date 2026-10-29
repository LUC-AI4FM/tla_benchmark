---- MODULE PrimingSemantics ----
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES x, y

vars == <<x, y>>

\* Helper operators
F(a) == a + 1
G == x + y
H(a, b) == IF a > b THEN a ELSE b
Sum == x + y
Inc(v) == (v + 1) % N

TypeOK ==
    /\ x \in 0..(N - 1)
    /\ y \in 0..N

Init ==
    /\ x = 0
    /\ y = 0
    /\ Print(<<"Init", x, y>>, TRUE)

Next ==
    /\ x' = Inc(x)
    /\ y' = F(x)
    \* Priming a direct variable reference
    /\ Assert(x' = (x + 1) % N, "Direct variable priming failed")
    /\ Assert(y' = x + 1, "Primed y must equal F applied to unprimed x")
    \* Priming an operator call with no arguments: G' = x' + y'
    /\ Assert(G' = x' + y', "Priming of zero-arity operator G failed")
    /\ Assert(Sum' = G', "Sum' and G' must coincide")
    \* Priming an operator application: F(x)' = F(x')
    /\ Assert((F(x))' = F(x'), "Priming of operator application F(x) failed")
    /\ Assert((F(x))' = x' + 1, "F(x)' must equal x' + 1")
    \* Priming of operator applied to a constant argument is unaffected
    /\ Assert((F(3))' = F(3), "Priming a constant expression must be identity")
    \* Priming a two-argument operator application
    /\ Assert((H(x, y))' = H(x', y'), "Priming of H(x, y) failed")
    \* Priming of LET-bound names: the definition is expanded then primed
    /\ LET z == x
           w == x + y
           c == 7
       IN  /\ Assert(z' = x', "LET-bound z' must equal x'")
           /\ Assert(w' = x' + y', "LET-bound w' must equal x' + y'")
           /\ Assert(c' = c, "LET-bound constant primed must be unchanged")
           /\ Assert(z = x, "Unprimed LET-bound z must equal x")
    \* LET whose body is primed as a whole
    /\ Assert((LET u == x IN u + y)' = x' + y', "Priming whole LET expression failed")
    \* Priming conditional expressions
    /\ Assert((IF x = 0 THEN y ELSE x)' = (IF x' = 0 THEN y' ELSE x'),
              "Priming of IF-THEN-ELSE failed")
    /\ IF x' > 0
          THEN Assert(y' = x + 1, "THEN branch: y' must be x + 1")
          ELSE Assert(x' = 0, "ELSE branch: x' must be 0")
    \* Priming a CASE expression
    /\ Assert((CASE x = 0 -> y [] OTHER -> x)' =
              (CASE x' = 0 -> y' [] OTHER -> x'),
              "Priming of CASE expression failed")
    /\ PrintT(<<"Step", x, y, x', y'>>)

Inv == TRUE

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Spec => []Inv
THEOREM Spec => []TypeOK
====