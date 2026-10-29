---------------------------- MODULE CyclicCounter ----------------------------
EXTENDS Naturals

VARIABLE x

---------------------------- MODULE AbstractProps ----------------------------
EXTENDS Naturals

CONSTANT Limit
VARIABLE y

\* Operator defined in the abstract module, passed back as an argument
Id(n) == n

\* Innermost predicate: applies operator argument to a state value
Pred(F(_), v) == F(v) \in Nat

\* Middle wrapper: routes the operator argument through another layer
Wrap(F(_), v) == Pred(F, v)

\* Outer wrapper: temporal property over the nested wrappers
Always(F(_), v) == [](Wrap(F, v))

\* Bounded property: may be violated depending on F and b
Bounded(F(_), v, b) == [](F(v) <= b)

\* State-only property: no operator argument
StateAlways(v) == [](v \in 0..Limit)

\* Trivial tautology
Taut == [](TRUE)
==============================================================================