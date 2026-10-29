---------------------------- MODULE Sum ----------------------------
EXTENDS Naturals

CONSTANTS Foo1, Foo2

\* The constants are assumed to be natural numbers.
ASSUME ConstAssump == Foo1 \in Nat /\ Foo2 \in Nat

\* The derived expression: the sum of the two constants.
Sum == Foo1 + Foo2

-----------------------------------------------------------------------------
\* There is no transition system, so the following are placeholders.
\* They are included only because the required structure asks for
\* Init, Next and Spec. They declare no variables and constrain nothing.

vars == <<>>

Init == TRUE

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Value-level properties of Sum (no fairness or liveness applies).

TypeOK == Sum \in Nat

SumCommutes == Sum = Foo2 + Foo1

SumBounds == Sum >= Foo1 /\ Sum >= Foo2

THEOREM Spec => [](TypeOK /\ SumCommutes /\ SumBounds)
=============================================================================