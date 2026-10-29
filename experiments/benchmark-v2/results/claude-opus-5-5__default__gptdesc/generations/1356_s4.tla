------------------------------ MODULE ParamOpsInstance ------------------------------
EXTENDS Naturals

VARIABLE s

----------------------------------------------------------------------------
(* Abstract module, used through INSTANCE with operator parameters.      *)
----------------------------------------------------------------------------

------------------------------ MODULE AbstractOps ------------------------------
EXTENDS Naturals

CONSTANT C(_)          \* a constant operator parameter
VARIABLE v             \* the abstract state variable

\* Apply the constant operator parameter
ApplyC(n) == C(n)

\* A state predicate built from an operator argument
Holds(P(_)) == P(v)

\* Temporal wrappers taking operator arguments
AlwaysHolds(P(_))     == [](P(v))
EventuallyHolds(P(_)) == <>(P(v))
InfOften(P(_))        == []<>(P(v))

\* Route a numeric-valued operator (e.g. a recursive one) through a check
AlwaysAtLeast(F(_), k) == [](F(v) >= k)

\* Route a binary operator through an action-level property
AlwaysStep(R(_, _)) == [][R(v, v')]_v

\* Leads-to wrapper
LeadsToW(P(_), Q(_)) == P(v) ~> Q(v)
================================================================================