---------------------------- MODULE OpParamInstance ----------------------------
EXTENDS Naturals

VARIABLE s

---------------------------- MODULE Abstract ----------------------------------
EXTENDS Naturals

VARIABLE x

\* Apply an operator argument to the abstract variable
Apply(F(_)) == F(x)

\* Temporal property parameterized by a unary operator
AlwaysNat(F(_)) == [](F(x) \in Nat)

\* Temporal property parameterized by a unary operator and a bound
AlwaysBounded(F(_), b) == [](F(x) <= b)

\* Temporal property parameterized by a nullary (constant) operator
AlwaysPred(P) == []P

\* Eventual property parameterized by a unary operator
InfOften(F(_), v) == []<>(F(x) = v)
================================================================================