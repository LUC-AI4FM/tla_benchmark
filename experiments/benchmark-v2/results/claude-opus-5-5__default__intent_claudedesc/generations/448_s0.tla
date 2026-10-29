---------------------------- MODULE VarExpr ----------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

\* Derived computation: successor of the current value (does not modify state)
Succ == x + 1

TypeOK == x \in Nat

Init == x = 0

\* The module is primarily definitional; the state is left unchanged.
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

\* Safety invariants
SuccCorrect == Succ = x + 1

THEOREM Spec => [](TypeOK /\ SuccCorrect)
=============================================================================