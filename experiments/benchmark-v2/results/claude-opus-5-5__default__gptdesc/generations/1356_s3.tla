------------------------------- MODULE ParamInstance -------------------------------
EXTENDS Naturals

VARIABLE s

vars == s

-----------------------------------------------------------------------------
(* Abstract module, defined inline as a submodule and used through INSTANCE.   *)
(* Its operators take operator parameters, so concrete, recursive and          *)
(* constant operators can be passed through the instantiation.                 *)
-----------------------------------------------------------------------------

------------------------------- MODULE Abstract --------------------------------
CONSTANTS F(_), C
VARIABLE v

\* P holds of v in every state
AlwaysP(P(_)) == [](P(v))

\* P eventually holds of v
EventuallyP(P(_)) == <>(P(v))

\* The value of G at v never exceeds its value at the bound k
AlwaysBelow(G(_), k) == [](G(v) <= G(k))

\* Property built from the constant operator parameter F and the constant C
FBelowC == [](F(v) <= F(C))

\* Trivial leads-to tautology over a parameterized predicate
LeadsToTaut(P(_)) == P(v) ~> P(v)
=================================================================================